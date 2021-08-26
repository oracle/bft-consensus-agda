{-# OPTIONS --allow-unsolved-metas #-}

{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore          as BlockStore
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.Liveness.ExponentialTimeInterval as ExponentialTimeInterval
import      LibraBFT.Impl.Consensus.Liveness.RoundState              as RoundState
import      LibraBFT.Impl.Consensus.MetricsSafetyRules               as MetricsSafetyRules
import      LibraBFT.Impl.Consensus.RoundManager                     as RoundManager
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRulesManager   as SafetyRulesManager
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage            as MockStorage
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-1  as ECP-LBFT-OBM-Diff-1
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.OBM.Rust.Duration                          as Duration
open import LibraBFT.Impl.OBM.Rust.RustTypes
import      LibraBFT.Impl.Storage.DiemDB.DiemDB                      as DiemDB
import      LibraBFT.Impl.Types.BlockInfo                            as BlockInfo
import      LibraBFT.Impl.Types.EpochChangeProof                     as EpochChangeProof
import      LibraBFT.Impl.Types.ValidatorVerifier                    as ValidatorVerifier
open import LibraBFT.Impl.Types.Verifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                              as String

module LibraBFT.Impl.Consensus.EpochManager where

open import LibraBFT.ImplShared.Util.Dijkstra.RWS        public
open import LibraBFT.ImplShared.Util.Dijkstra.RWS.Syntax public

------------------------------------------------------------------------------

data RlecState : Set where
  RSNothing  : RlecState
  RSNeedECP  : ReconfigEventEpochChange → RlecState
  RSNeedRLEC : EpochChangeProof         → RlecState

data ProcessMessageAction : Set where
  PMContinue        : ProcessMessageAction
  PMInput           : Input            → ProcessMessageAction
  PMNewEpochManager : EpochManager     → List Output    → ProcessMessageAction
  PMSendECP         : EpochChangeProof → AccountAddress → Author {-Text-} → Epoch → Round → ProcessMessageAction
  PMSendEpochRRq    : EpRRqWire        → AccountAddress → ProcessMessageAction

data PMOutput : Set where
  PMErr  : ErrLog  → PMOutput
  PMInfo : InfoLog → PMOutput

EM : Set → Set₁
EM = RWS Unit PMOutput RlecState

runEM : ∀ {r}
      → EM r
      → RlecState
      → (r × RlecState × List PMOutput)
runEM f = RWS-run f unit

------------------------------------------------------------------------------

expectNewEpoch
  : EpochManager → Instant → ReconfigEventEpochChange → LedgerInfoWithSignatures
  → Either ErrLog ProcessMessageAction

startProcessor
  : EpochManager → Instant → OnChainConfigPayload
  → ObmNeedFetch → ProposalGenerator → LedgerInfoWithSignatures
  → Either ErrLog  (EpochManager × List Output)

startRoundManager'
  : EpochManager → Instant → RecoveryData → EpochState
  → ObmNeedFetch → ProposalGenerator → Version
  → Either ErrLog (EpochManager × List Output)

------------------------------------------------------------------------------

new
  : NodeConfig → {-StateComputer →-} PersistentLivenessStorage → Author → SK
  → Either ErrLog EpochManager
new nodeConfig {-stateComputer-} persistentLivenessStorage obmAuthor obmSK = do
  let -- author = node_config.validator_network.as_ref().unwrap().peer_id();
      config = nodeConfig ^∙ ncConsensus
  safetyRulesManager ← SafetyRulesManager.new (config ^∙ ccSafetyRules) obmAuthor obmSK
  pure $ mkEpochManager
    obmAuthor
    config
    --stateComputer
    persistentLivenessStorage
    safetyRulesManager
    nothing

epochState : EpochManager → Either ErrLog EpochState
epochState self = case self ^∙ emProcessor of λ where
  nothing                           → Left fakeErr -- ["EpochManager not started yet"]
  (just (RoundProcessorNormal   p)) → pure (p ^∙ rmEpochState)
  (just (RoundProcessorRecovery p)) → pure (p ^∙ rcmEpochState)

epoch : EpochManager → Either ErrLog Epoch
epoch self = (_^∙ esEpoch) <$> epochState self

createRoundState : EpochManager → Instant → RoundState
createRoundState self now =
  let timeInterval = ExponentialTimeInterval.new
        (Duration.fromMillis (self ^∙ emConfig ∙ ccRoundInitialTimeoutMS))
        1.2
        6
   in RoundState.new timeInterval now

createProposerElection : EpochState → ProposerElection
createProposerElection epochState0 =
  ProposerElection∙new -- TODO-1
  -- (ValidatorVerifier.getOrderedAccountAddressesObmTODO (epochState0 ^∙ esVerifier))

processEpochRetrieval
  : EpochManager {-Text-} → EpRRqWire → AccountAddress → EM ProcessMessageAction
processEpochRetrieval self {-wireOrInternal-} (EpRRqWire∙new {-why fromE fromR-} request) peerAddress = do
  tell (PMInfo fakeInfo ∷ [])
    -- ["Enter", wireOrInternal, why, lsA peerAddress, lsE fromE, lsR fromR, lsEpochRRq request]))]
  case DiemDB.getEpochEndingLedgerInfos
         (self ^∙ emStorage ∙ msObmDiemDB) (request ^∙ eprrqStartEpoch) (request ^∙ eprrqEndEpoch) of λ where
    (Left e) → do
      tell ( (PMErr (withErrCtx (here'
               ("failed to get epoch proof" {-lsA peerAddress, why, lsEpochRRq request-} ∷ [])) e))
           ∷ [])
      pure PMContinue
    (Right (liws , more)) →
      eitherSD (self ^∙ emEpoch) (λ err -> do tell (PMErr (withErrCtx (here' []) err) ∷ []); pure PMContinue) $ λ e -> do
          let ecp = EpochChangeProof∙new liws more
              me  = self ^∙ emAuthor
              r   = eitherS (self ^∙ emObmRoundManager) (const {-Round-} 0) (_^∙ rmRound)
          tell (PMInfo fakeInfo {-["Exit", "SendEpochRRp", why, lsA peerAddress, lsECP ecp]-} ∷ [])
          pure (PMSendECP ecp peerAddress me {-why-} e r)
 where
  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "processEpochRetrieval" ∷ t

processDifferentEpoch
  : EpochManager → Input → AccountAddress → Epoch → Round
  → EM ProcessMessageAction
processDifferentEpoch self obmI peerAddress peerDifferentEpoch obmPeerRound = do
  tell (PMInfo fakeInfo -- (here [ "ReceiveMessageFromDifferentEpoch", lsA peerAddress
                        --       , lsE peerDifferentEpoch, lsR obmPeerRound, logShowI obmI ])
                        ∷ [])
  eitherSD (self ^∙ emEpoch) (λ err → do tell (PMErr (withErrCtx (here' []) err) ∷ []); pure PMContinue) $ λ epoch' →
    --eitherSD (self ^∙ emObmRoundManager) (λ err -> do tell (PMErr (withErrCtx (here' []) err) :: []); pure PMContinue) $ λ rm →
      case compare peerDifferentEpoch epoch' of λ where
        LT → do -- help nodes that have lower epoch
          -- LBFT-OBM-DIFF : not sure if this is different, but the message that causes
          -- this request will be dropped.
          -- await (Rust comment)
          processEpochRetrieval
            self {-"diffE"-}
            (EpRRqWire∙new {-why epoch' (self^.emObmRoundManagerErrExit.rmRound)-}
              (EpochRetrievalRequest∙new peerDifferentEpoch epoch'))
            peerAddress
        GT → do
          -- LBFT-OBM-DIFF : message dropped in this case too
          let epRrq  = EpochRetrievalRequest∙new epoch' peerDifferentEpoch
              epprqw = EpRRqWire∙new {-why epoch' (self^.emObmRoundManagerErrExit.rmRound)-} epRrq
          tell (PMInfo fakeInfo ∷ [])
                     -- (here [ "SendEpochRRq", lsA peerAddress, lsEpochRRq epRrq
                     --       , "request proof to join higher epoch because", logShowI obmI ]))]
          -- TODO-1
          pure (PMSendEpochRRq epprqw peerAddress)
        EQ → do
          tell (PMErr fakeErr ∷ []) -- (here ["EQ should not happen"])
          pure PMContinue
 where
  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "processDifferentEpoch" ∷ t
{-
  why    = show (msgType obmI)               <> "/" <>
           peerAddress^.aAuthorName          <> "/" <>
           show (peerDifferentEpoch^.eEpoch) <> "/" <>
           show (obmPeerRound^.rRound)
-}

startNewEpoch
  : EpochManager → Instant → Maybe ReconfigEventEpochChange → EpochChangeProof
  → Either ErrLog ProcessMessageAction
startNewEpoch self now mrlec proof = do
  es   ← epochState self
  liws ← withErrCtx' (here' ("invalid EpochChangeProof" ∷ []))
                     (EpochChangeProof.verify proof es)
  -- --------------------------------------------------
  -- LBFT-OBM-DIFF: scSyncTo, rather than syncing world state to another node,
  -- it just gets the NextEpochState from the given LIWS.
  -- --------------------------------------------------
  -- Independently, the world state is synced to the Version/LeadCount contained in 'liws'.
  -- See 'obmVersion' setting in startRoundManager' below.
  rlec ← case mrlec of λ where
           (just rlec) → pure rlec
           nothing     → eitherS (Left "fakeErr") -- TODO-2 ((self^.emStateComputer.scSyncTo) liws)
                                 (λ e → Left fakeErr) -- (ErrL (here (lsLIWS liws ∷ e))))
                                 Right
  self' ← ECP-LBFT-OBM-Diff-1.e_EpochManager_startNewEpoch self proof
  pure PMContinue
  expectNewEpoch self' now rlec liws
 where
  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "startNewEpoch" ∷ t

startRoundManager
  : EpochManager → Instant → RecoveryData → EpochState
  → ObmNeedFetch → ProposalGenerator → Version
  → Either ErrLog (EpochManager × List Output)
startRoundManager self0 now recoveryData epochState0 obmNeedFetch obmProposalGenerator obmVersion =
  let self = case self0 ^∙ emProcessor of λ where
               (just (RoundProcessorNormal rm)) →
                 self0 & emStorage               ∙~ rm ^∙ rmBlockStore ∙ bsStorage
                       & emStorage ∙ msObmDiemDB ∙~ self0 ^∙ emStorage ∙ msObmDiemDB
               _ →
                 self0
      -- OBM-DIFF : use the version in the ledger info of the EpochChangeProof
      obv  = eitherS (self ^∙ emObmRoundManager) (const BlockInfo.gENESIS_VERSION) (const obmVersion)

   in startRoundManager' self now recoveryData epochState0 obmNeedFetch
                         (obmProposalGenerator & pgLastRoundGenerated ∙~ {-Round-} 0)
                         obv

startRoundManager' self now recoveryData epochState0 obmNeedFetch obmProposalGenerator obv = do
  let lastVote = recoveryData ^∙ rdLastVote
  case BlockStore.new
         (self ^∙ emStorage)
         recoveryData
         -- TODO-2 : use real StateComputer when it exists
         stateComputer -- (self ^∙ emStateComputer & scObmVersion .~ obv) TODO-2
         (self ^∙ emConfig ∙ ccMaxPrunedBlocksInMem) of λ where
    (Left  e) -> err ("BlockStore.new" ∷ []) e
    (Right r) -> continue1 lastVote r
 where
  err : ∀ {B} → List String.String → ErrLog → Either ErrLog B
  err  t = withErrCtx' t ∘ Left
  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "startRoundManager" ∷ t

  continue2 : Maybe Vote → BlockStore → SafetyRules → Either ErrLog (EpochManager × List Output)

  continue1 : Maybe Vote → BlockStore → Either ErrLog (EpochManager × List Output)
  continue1 lastVote blockStore = do
    --------------------------------------------------
    let safetyRules = {-MetricsSafetyRules::new-}
          SafetyRulesManager.client (self ^∙ emSafetyRulesManager) -- self.storage.clone());
    case MetricsSafetyRules.performInitialize safetyRules (self ^∙ emStorage) of λ where
      (Left e)             → err (here' ("MetricsSafetyRules.performInitialize" ∷ [])) e
      (Right safetyRules') → continue2 lastVote blockStore safetyRules'

  continue2 lastVote blockStore safetyRules = do
    --------------------------------------------------
    let proposalGenerator = obmProposalGenerator
    --------------------------------------------------
    let roundState = createRoundState self now
    --------------------------------------------------
    let proposerElection = createProposerElection epochState0
    --------------------------------------------------
    let processor = RoundManager∙new
          obmNeedFetch
          epochState0
          blockStore
          roundState
          proposerElection
          proposalGenerator
          (safetyRules & srPersistentStorage ∙ pssSafetyData ∙ sdEpoch ∙~ epochState0 ^∙ esEpoch)
          (self ^∙ emConfig ∙ ccSyncOnly)
    --------------------------------------------------
    let (_ , processor' , output) = LBFT-run (RoundManager.start now lastVote) processor
    case findFirstErr output of λ where
      (just e) → err (here' ("RoundManager.start" ∷ [])) e
      nothing  → pure ( (self & emProcessor ?~ RoundProcessorNormal processor')
                      , output )
   where
    findFirstErr : List Output → Maybe ErrLog
    findFirstErr = λ where
      []              → nothing
      (LogErr e ∷ xs) → just e
      (_        ∷ xs) → findFirstErr xs

startProcessor self now payload obmNeedFetch obmProposalGenerator obmLedgerInfoWithSignatures = do
  let validatorSet = payload ^∙ occpObmValidatorSet
      epochState0  = EpochState∙new (payload ^∙ occpEpoch) (ValidatorVerifier.from validatorSet)
      -- OBM TODO case storage.start of RecoveryData | LedgerRecoveryData
  (initialData , _pls)
                   ← MockStorage.startForTesting validatorSet
                                                 (just obmLedgerInfoWithSignatures)
  startRoundManager self now initialData epochState0 obmNeedFetch obmProposalGenerator
                    (obmLedgerInfoWithSignatures ^∙ liwsLedgerInfo ∙ liVersion)


processMessage
  : EpochManager → Instant → Input
  → EM ProcessMessageAction
processMessage self now = λ where
  a@(IBlockRetrievalRequest  _ _) → pure (PMInput a)
  a@(IBlockRetrievalResponse _ _) → pure (PMInput a)
  (IEpochChangeProof from (ECPWire∙new {-why e r-} ecp))
                                  → do
                                    tell (PMInfo fakeInfo ∷ [])
                                     --[ "processEpochChangeProof"
                                     -- , why, lsA from, lsE e, lsR r, lsECP ecp ]))]
                                    doECP ecp
  (IEpochRetrievalRequest frm a@(EpRRqWire∙new {- _why _e _r -} epRrq))
                                  → eitherSD (self ^∙ emEpoch)
                                             (λ e -> do tell (PMErr (withErrCtx (here' []) e) ∷ [])
                                                        pure PMContinue)
                                             $ λ epoch' →
                                        ifD (epRrq ^∙ eprrqEndEpoch >? epoch')
                                        then (do
                                          tell (PMInfo fakeInfo ∷ [])
                                             --["EpochRRq beyond ours", why, lsE (epRrq^.eprrqEndEpoch)]))]
                                          pure PMContinue)
                                        else processEpochRetrieval self {-"wire"-} a frm
  a@(IInit _)                     → pure (PMInput a)
  a@(IProposal _ from pm)         → maybeDifferentEpoch a from (pm ^∙ pmEpoch) (pm ^∙ pmRound)
  (IReconfigLocalEpochChange rlec) → do
                                     tell (PMInfo fakeInfo ∷ []) --(here ["receive", lsRLEC rlec]))]
                                     doRLEC rlec
  a@(ISyncInfo _ from si)         → case
                                      ECP-LBFT-OBM-Diff-1.e_EpochManager_processMessage_ISyncInfo
                                        self si of λ where
                                      (Left  e) → do tell (PMErr e ∷ [])
                                                     pure PMContinue
                                      (Right _) →
                                        maybeDifferentEpoch a from (si ^∙ siEpoch) (si ^∙ siObmRound)
  a@(ITimeout _ _ _ _)            → pure (PMInput a)
  a@(IVote _ from vm)             → maybeDifferentEpoch a from (vm ^∙ vmEpoch) (vm ^∙ vmRound)
 where
  doRlecEcp : Maybe ReconfigEventEpochChange → EpochChangeProof → EM ProcessMessageAction

  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "processMessage" ∷ t

  maybeDifferentEpoch : Input → AccountAddress → Epoch → Round → EM ProcessMessageAction
  maybeDifferentEpoch a from e r =
    eitherSD (self ^∙ emEpoch) (λ err → do tell (PMErr (withErrCtx (here' []) err) ∷ []); pure PMContinue) $ λ epoch' →
        ifD e == epoch'
        then pure (PMInput a)
        else processDifferentEpoch self a from e r

  doECP : EpochChangeProof → EM ProcessMessageAction
  doECP ecp = get >>= λ where
    RSNothing → case ECP-LBFT-OBM-Diff-1.e_EpochManager_checkEpc self ecp of λ where
      (Left e)  → do
        tell (PMErr e ∷ [])
        pure PMContinue
      (Right _) → do
       eitherSD (ECP-LBFT-OBM-Diff-1.e_EpochManager_doECP_waitForRlec self ecp)
                (λ e → do tell (PMErr (withErrCtx (here' []) e) ∷ []); pure PMContinue)
                $ λ b →
        ifD b
          then (do
          tell (PMInfo fakeInfo ∷ []) -- [ "doECP", "got ECP", "waiting for RLEC"
                                      -- , "my epoch", lsEE (self^.emEpoch), lsECP ecp])]
          put (RSNeedRLEC ecp)
          pure PMContinue)
          else do
          tell (PMInfo fakeInfo ∷ []) -- ["doECP", "got ECP", "NOT waiting for RLEC"
                                      -- , "my epoch", lsEE (self^.emEpoch), lsECP ecp])]
          put RSNothing
          doRlecEcp nothing ecp
    (RSNeedRLEC ecpX) → do
        tell (PMInfo fakeInfo ∷ []) -- ["got another ECP while waiting for RLEC", lsECP ecp, lsECP ecpX])]
        pure PMContinue  -- TODO
    (RSNeedECP rlec) → do
        put RSNothing
        doRlecEcp (just rlec) ecp

  doRLEC : ReconfigEventEpochChange → EM ProcessMessageAction
  doRLEC rlec = get >>= λ where
    RSNothing → do
        tell (PMInfo fakeInfo ∷ []) -- ["doRLEC", "got RLEC", "waiting for ECP", lsRLEC rlec])]
        put (RSNeedECP rlec)
        pure PMContinue
    (RSNeedRLEC ecp) → do
        put  RSNothing
        doRlecEcp (just rlec) ecp
    (RSNeedECP rlecX) → do
        tell (PMInfo fakeInfo ∷ [])
             -- ["doRLEC", "got another RLEC while waiting for ECP", lsRLEC rlec, lsRLEC rlecX])]
        pure PMContinue  -- TODO

  doRlecEcp rlec ecp =
    case startNewEpoch self now rlec ecp of λ where
      (Left err) → do
        tell (PMErr err ∷ [])
        pure PMContinue
      (Right r) → pure r

expectNewEpoch self now (ReconfigEventEpochChange∙new payload) obmLedgerInfoWithSignatures = do
  rm       ← self ^∙ emObmRoundManager
  (em , o) ← startProcessor self now payload
               (rm ^∙ rmObmNeedFetch)
               (rm ^∙ rmProposalGenerator)
               obmLedgerInfoWithSignatures
  pure (PMNewEpochManager em o)

start
  : EpochManager → Instant
  → OnChainConfigPayload → ObmNeedFetch → ProposalGenerator → LedgerInfoWithSignatures
  → Either ErrLog (EpochManager × List Output)
start self0 now obmPayload obmNeedFetch obmProposalGenerator obmLedgerInfoWithSignatures =
  startProcessor self0 now obmPayload obmNeedFetch obmProposalGenerator obmLedgerInfoWithSignatures

------------------------------------------------------------------------------
-- IMPL-DIFF
{-
'obmStartLoop' is the function that
- gets input (e.g., from the network)
- runs that input through the EpochManager in the 'EM' monad
- logs any errors that happen in the EpochManager
- dispatches on the output of the EpochManager
  - in some  cases it runs the RoundManager in the LBFT monad
  - in other cases it sends messages (via 'stps') to other nodes

The following "implementation" compiles, but has lots of TEMPORARY things to get it to compile.
-}

IO : Set → Set₁
IO = RWS Unit Unit Unit

{-# TERMINATING #-}
obmStartLoop
  : EpochManager → List Output
  {-→ CLI.FakeNetworkDelay → DAR.DispatchConfig a → INPUT_CHANNEL_READ a-}
  → IO Unit
obmStartLoop self initializationOutput
             {-(CLI.FakeNetworkDelay fnd)
             (DAR.DispatchConfig _rm0 toDAR ih oh lg lc stps m)
             lbftInR-} = do
  case self ^∙ emObmRoundManager of λ where
    (Left   e) → (errorExit ∘ here' ∘ singleShow) e
    (Right rm) → do
      -- This line roughly corresponds to Rust expect_new_epoch.
      -- It processes the output from start/startProcessor above.
      -- TODO (rm' , to') ← DAR.runOutputHandler rm toDAR pe initializationOutput oh
      rm'                 ← pure rm -- TEMPORARY for previous line
      loop (setProcessor self rm') {-to'-} RSNothing
 where
  show : ∀ {A : Set} → A → String.String
  show _ = ""

  singleShow : ∀ {A : Set} → A → List String.String
  singleShow {A} x = show {A} x ∷ []

  errorExit : List String.String → IO Unit
  errorExit _ = pure unit

  here' : List String.String → List String.String
  here' t = "EpochManager" ∷ "obmStartLoop" ∷ t

  setProcessor : EpochManager → RoundManager → EpochManager
  setProcessor em p = em & emProcessor ?~ RoundProcessorNormal p

  loop : EpochManager {-→ Map ScheduledInputKey ThreadId-} → RlecState → IO Unit
  loop em {-to-} rlec0 = do
    -- i ← U.readChan lbftInR
    i ← pure (IInit 0) -- TEMPORARY for previous line
    -- when (fnd > 0) $
    --  threadDelay (fnd * oneMillisecond)
    -- now                    ← Time.getCurrentInstant
    now                    ← pure (0) -- TEMPORARY for previous line
    let (pma , rlec , pmo) = runEM (processMessage em now i) rlec0
    let myName             = em ^∙ emAuthor ∙ aAuthorName
    forM_ pmo $ λ where
      -- (PMErr  (ErrInfo (lc', x)) → Logger.log (lg myName) lc (LogInfo lc' x)
      (PMErr  x)                        → pure unit -- Logger.log (lg myName) lc (LogErr      x)
      (PMInfo x)                        → pure unit -- Logger.log (lg myName) lc (LogInfo lEC x)
    case pma of λ where
      PMContinue →
        loop em {-to-} rlec
      (PMInput i') →
       eitherSD (em ^∙ emObmRoundManager) (errorExit ∘ here' ∘ singleShow) $ λ rm → do
        --(rm'  ,    o) ← DAR.runInputHandler  rm  to pe i' ih
        --(rm'' , to'') ← DAR.runOutputHandler rm' to pe o  oh
        rm'' ← pure rm -- TEMPORARY for previous two lines
        loop (setProcessor em rm'') {-to''-} rlec
      (PMNewEpochManager em' newEpochInitializationOutput) → do
       eitherSD (em' ^∙ emObmRoundManager) (errorExit ∘ here' ∘ singleShow) $ λ rm → do
        -- (rm', to') ← DAR.runOutputHandler   rm  to pe newEpochInitializationOutput oh
        rm' ← pure rm -- TEMPORARY for previous line
        loop (setProcessor em' rm') {-to'-} rlec -- TODO Set₁ != Set
      (PMSendECP ecp peerAddress me {-why-} e r) → do
        -- stps [peerAddress ^∙ aAuthorName] (Messages.mkIEpochChangeProof me why e r ecp)
        loop em {-to-} rlec
      (PMSendEpochRRq epRrq sendTo) → do
        -- stps [sendTo ^∙ aAuthorName] (IEpochRetrievalRequest (em ^∙ emAuthor) epRrq)
        loop em {-to-} rlec
{-
  pe = PeerEnv
    (""::Text)
    Map.empty
    (RunEnv
      (lg (self ^∙ emAuthor.aAuthorName))
      lc
      (Just stps)
      (Just m))
-}
