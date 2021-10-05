{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.Liveness.RoundState as RoundState
import      LibraBFT.Impl.IO.OBM.GenKeyFile             as GenKeyFile
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
import      LibraBFT.Impl.IO.OBM.Start                  as Start
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Time
import      LibraBFT.Impl.Types.BlockInfo               as BlockInfo
import      LibraBFT.Impl.Types.ValidatorSigner         as ValidatorSigner
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
import      LibraBFT.Yasm.Types as LYT
open import Optics.All

-- This module provides scaffolding to define handlers for the implementation model and
-- to connect those handlers to the interface of the SystemModel.

module LibraBFT.Impl.Handle where

open EpochConfig

------------------------------------------------------------------------------

-- This invokes the real implementation handler.
runHandler : RoundManager → LBFT Unit → RoundManager × List (LYT.Action NetworkMsg)
runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

-- NOTE: The system layer only cares about this step function.
-- 0 is given as a timestamp.
peerStep : NodeId → NetworkMsg → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
peerStep nid msg st = runHandler st (handle nid msg 0)

------------------------------------------------------------------------------
-- BEGIN fake initialization - TODO : DELETE

postulate -- TODO-1: reasonable assumption that some RoundManager exists, though we could prove
          -- it by construction; eventually we will construct an entire RoundManager, so
          -- this won't be needed

  -- This represents an uninitialised RoundManager, about which we know nothing, which we use as
  -- the initial RoundManager for every peer until it is initialised.
  fakeRM : RoundManager

postulate -- TODO-2: define BootstrapInfo to match implementation and write these functions
  fakeInitVV  : BootstrapInfo → ValidatorVerifier

fakeInitSR : SafetyRules
fakeInitSR =
  let sr = fakeRM ^∙ lSafetyRules
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound ∙~ 0
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdEpoch          ∙~ 1
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVote       ∙~ nothing
  in sr

fakeInitPG : ProposalGenerator
fakeInitPG = ProposalGenerator∙new 0

postulate -- TODO-1: fakeInitPE, fakeInitBS, fakeInitRS
  fakeInitPE : ProposerElection
  fakeInitBS : BlockStore
  fakeInitRS : RoundState

-- TODO-1 : postulate
fakeInitRM : RoundManager
fakeInitRM = RoundManager∙new
           ObmNeedFetch∙new
           (EpochState∙new 1 (fakeInitVV fakeBootstrapInfo))
           fakeInitBS fakeInitRS fakeInitPE fakeInitPG fakeInitSR false

-- Eventually, the initialization should establish properties we care about.
-- For now we just initialise to fakeRM.
-- That means we cannot prove the base case for various properties,
-- e.g., in Impl.Properties.VotesOnce
-- TODO: create real RoundManager using LibraBFT.Impl.IO.OBM.Start
fakeInitialRoundManagerAndMessages
  : (a : Author) → BootstrapInfo
  → RoundManager × List NetworkMsg
fakeInitialRoundManagerAndMessages a _ = fakeInitRM , []

-- TODO-2: These "wrappers" can probably be shared with FakeImpl, and therefore more of this could
-- be factored into LibraBFT.ImplShared.Interface.* (maybe Output, in which case maybe that should
-- be renamed?)

fakeInitWrapper : NodeId → BootstrapInfo → RoundManager × List (LYT.Action NetworkMsg)
fakeInitWrapper nid g = ×-map₂ (List-map LYT.send) (fakeInitialRoundManagerAndMessages nid g)

fakeInitAndHandlers : SystemInitAndHandlers ℓ-RoundManager ConcSysParms
fakeInitAndHandlers = mkSysInitAndHandlers
                    fakeBootstrapInfo
                    fakeInitRM
                    (λ pid bootstrapInfo → just (fakeInitWrapper pid bootstrapInfo))
                    peerStep
-- END fake initialization - TODO : DELETE
------------------------------------------------------------------------------

module RealHandler
  --(bsi0 : BootstrapInfo) -- TODO-1 : properties about BootstrapInfo
  where

  ------------------------------------------------------------------------------
  -- real initialization

  {-
  IMPL-DIFF: In Haskell, nodes are started with a filepath of a file containing
  - number of faults allowed
  - genesis LedgerInfoWithSignatures
  - network addresses/name and secret and public keys of all nodes in the genesis epoch

  Main reads/checks that file then calls a network specific 'run' functions (e.g., ZMQ.hs)
  that setup the network handlers then eventually call 'Start.startViaConsensusProvider'.

  That functions calls 'ConsensusProvider.startConsensus' which returns
  '(EpochManager, [Output]'.

  'Start.startViaConsensusProvider' then goes on to create and wire up internal communication
  channels and starts threads.  The most relevant thread starts up
  `(EpochManager.obmStartLoop epochManager output ...)' to handle the initialization output
  and then to handle new messages from the network.

  In Agda functions below, assuming no initialization errors,
  - the 'GenKeyFile.create' function
    - creates everything that would have been written to disk and then later read
      to create ValidatorSigner(s), ValidatorVerifier, LIWS, etc.
  - there is no network transport in Agda
  - 'initialize' calls 'State.startViaConsensusProvider'
    when then calls 'ConsensusProvider.startConsensus' which returns
    '(EpochManager, List Output)', just like Haskell.
  - Since there is no network, internal channels and threads, this is the end of this process.

  Note: although both the Haskell and Agda version support non-uniform voting, the
  above initialization process assumes one-vote per peer.
  -}

  postulate
    now           : Instant
    pg            : ProposalGenerator

  initialize' : Instant → GenKeyFile.NfLiwsVsVvPe → Either ErrLog (EpochManager × List Output)
  initialize' now nfLiwsVsVvPe =
    Start.startViaConsensusProvider
      now nfLiwsVsVvPe
      (TxTypeDependentStuffForNetwork∙new pg (StateComputer∙new BlockInfo.gENESIS_VERSION))

  abstract
    initialize  : Instant → GenKeyFile.NfLiwsVsVvPe → Either ErrLog (EpochManager × List Output)
    initialize  = initialize'
    initialize≡ : initialize ≡ initialize'
    initialize≡ = refl

  mkNfLiwsVsVvPe : BootstrapInfo → ValidatorSigner → GenKeyFile.NfLiwsVsVvPe
  mkNfLiwsVsVvPe bsi vs = (bsi ^∙ bsiNumFaults , bsi ^∙ bsiLIWS , vs , bsi ^∙ bsiVV , bsi ^∙ bsiPE)

  initEMWithOutput' : BootstrapInfo → ValidatorSigner → Either  ErrLog (EpochManager × List Output)
  initEMWithOutput' bsi vs =
    initialize now (mkNfLiwsVsVvPe bsi vs)

  initEMWithOutput  : BootstrapInfo → ValidatorSigner → EitherD ErrLog (EpochManager × List Output)
  initEMWithOutput  bsi vs =
    fromEither $
    initialize now (mkNfLiwsVsVvPe bsi vs)

  getEmRm : EpochManager → Either ErrLog RoundManager
  getEmRm em =
    case em ^∙ emProcessor of λ where
      nothing  → Left fakeErr
      (just p) → case p of λ where
                   (RoundProcessorRecovery _) → Left fakeErr
                   (RoundProcessorNormal rm)  → Right rm

  initRMWithOutput' : BootstrapInfo → ValidatorSigner → Either  ErrLog (RoundManager × List Output)
  initRMWithOutput' bsi vs = do
    (em , lo) ← initEMWithOutput' bsi vs
    rm        ← getEmRm em
    Right (rm , lo)

  initRMWithOutput  : BootstrapInfo → ValidatorSigner → EitherD ErrLog (RoundManager × List Output)
  initRMWithOutput  bsi vs = do
    (em , lo) ← initEMWithOutput bsi vs
    rm        ← fromEither
              $ getEmRm em
    fromEither $ Right (rm , lo)

  -- This shows that the Either and EitherD versions are equivalent.
  -- This is a first step towards eliminating the painful VariantOf stuff,
  -- so we can have the version that looks (almost) exactly like the Haskell,
  -- and the EitherD variant, broken into explicit steps, etc. for proving.
  initEMWithOutput≡
    : ∀ {bsi : BootstrapInfo} {vs : ValidatorSigner}
    → initEMWithOutput' bsi vs ≡ EitherD-run (initEMWithOutput bsi vs)
  initEMWithOutput≡ {bsi} {vs}
    with initialize now (mkNfLiwsVsVvPe bsi vs)
  ... | Left  _ = refl
  ... | Right _ = refl

  initRMWithOutput≡
    : ∀ {bsi : BootstrapInfo} {vs : ValidatorSigner}
    → initRMWithOutput' bsi vs ≡ EitherD-run (initRMWithOutput bsi vs)
  initRMWithOutput≡ {bsi} {vs}
    with initialize now (mkNfLiwsVsVvPe bsi vs)
  ... | Left  _ = refl
  ... | Right (em , _)
    with getEmRm em
  ... | Left  _ = refl
  ... | Right _ = refl

  abstract
   realHandler : Author → BootstrapInfo → Maybe (RoundManager × List (LYT.Action NetworkMsg))
   realHandler pid bsi =
    case ValidatorSigner.obmGetValidatorSigner pid (bsi ^∙ bsiVSS) of λ where
      (Left _)   → nothing
      (Right vs) →
        case initRMWithOutput' bsi vs of λ where
          (Left _)          → nothing
          (Right (rm , lo)) → just (rm , outputsToActions {State = rm} lo)

  InitAndHandlers : SystemInitAndHandlers ℓ-RoundManager ConcSysParms
  InitAndHandlers =
    mkSysInitAndHandlers
      fakeBootstrapInfo -- bsi0
      fakeInitRM
      realHandler
      peerStep

