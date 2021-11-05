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

-- This module connects implementation handlers to the interface of the SystemModel.

module LibraBFT.Impl.Handle where

open EpochConfig

------------------------------------------------------------------------------
-- This function works with any implementation of a RoundManager.

-- NOTE: The system layer only cares about this step function.
-- 0 is given as a timestamp.
peerStep : NodeId → NetworkMsg → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
peerStep nid msg st = runHandler st (handle nid msg 0)
 where
  -- This invokes an implementation handler.
  runHandler : RoundManager → LBFT Unit → RoundManager × List (LYT.Action NetworkMsg)
  runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

------------------------------------------------------------------------------

-- This connects the implementation handler to the system model so it can be initialized.

module InitHandler where
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

  In Agda below,
  - we assume 'BootstrapInfo' known to all peers
    - i.e., the same info that Haskell creates via 'GenKeyFile.create'
    - the assumed info is given to 'mkSysInitAndHandlers' in 'InitAndHandlers'
  - System initialization calls 'initHandler'
  - 'initHandler' eventually calls 'initialize'
  - 'initialize' calls 'State.startViaConsensusProvider'
    when then calls 'ConsensusProvider.startConsensus' which returns
    '(EpochManager, List Output)', just like Haskell.
  - Since there is no network, internal channels and threads, this is the end of this process.

  Note: although both the Haskell and Agda version support non-uniform voting, the
  above initialization process assumes one-vote per peer.
  -}

  postulate -- TODO-2: Eliminate when/if timestamps are modeled
    now : Instant

  proposalGenerator : ProposalGenerator
  proposalGenerator = ProposalGenerator∙new 0

  initialize-e : Instant → GenKeyFile.NfLiwsVsVvPe → Either ErrLog (EpochManager × List Output)
  initialize-e now nfLiwsVsVvPe =
    Start.startViaConsensusProvider
      now nfLiwsVsVvPe
      (TxTypeDependentStuffForNetwork∙new
        proposalGenerator
        (StateComputer∙new BlockInfo.gENESIS_VERSION))

  postulate
    initialize-ed : Instant → GenKeyFile.NfLiwsVsVvPe → EitherD ErrLog (EpochManager × List Output)

  abstract
    initialize-e-abs  : Instant → GenKeyFile.NfLiwsVsVvPe
                    → Either ErrLog (EpochManager × List Output)
    initialize-e-abs  = initialize-e
    initialize-abs≡ : initialize-e-abs ≡ initialize-e
    initialize-abs≡ = refl

    initialize-ed-abs  = initialize-ed

  mkNfLiwsVsVvPe : BootstrapInfo → ValidatorSigner → GenKeyFile.NfLiwsVsVvPe
  mkNfLiwsVsVvPe bsi vs = (bsi ^∙ bsiNumFaults , bsi ^∙ bsiLIWS , vs , bsi ^∙ bsiVV , bsi ^∙ bsiPE)

  initEMWithOutput-e-unused  : BootstrapInfo → ValidatorSigner
                      → Either ErrLog (EpochManager × List Output)
  initEMWithOutput-e-unused bsi vs =
    initialize-e-abs now (mkNfLiwsVsVvPe bsi vs)

  -- No need to break this one into steps, no decision points
  initEMWithOutput-ed : BootstrapInfo → ValidatorSigner
                      → EitherD ErrLog (EpochManager × List Output)
  initEMWithOutput-ed  bsi vs =
    initialize-ed-abs now (mkNfLiwsVsVvPe bsi vs)

  abstract
    initEMWithOutput-e-abs : BootstrapInfo → ValidatorSigner
                           → Either ErrLog (EpochManager × List Output)
    initEMWithOutput-e-abs bsi vs = toEither $ initEMWithOutput-ed bsi vs

    initEMWithOutput-ed-abs = initEMWithOutput-ed
    initEMWithOutput-ed-abs≡ : initEMWithOutput-ed-abs ≡ initEMWithOutput-ed
    initEMWithOutput-ed-abs≡ = refl

    -- This shows that the Either and EitherD versions are equivalent.
    -- This is a first step towards eliminating the painful VariantOf stuff,
    -- so we can have the version that looks (almost) exactly like the Haskell,
    -- and the EitherD variant, broken into explicit steps, etc. for proving.
    initEMWithOutput≡
      : ∀ {bsi : BootstrapInfo} {vs : ValidatorSigner}
      → initEMWithOutput-e-abs bsi vs ≡ EitherD-run (initEMWithOutput-ed-abs bsi vs)
    initEMWithOutput≡ {bsi} {vs} = refl

  getEmRm-ed : EpochManager → EitherD ErrLog RoundManager
  getEmRm-ed em =
    case em ^∙ emProcessor of λ where
      nothing  → LeftD fakeErr
      (just p) → case p of λ where
                   (RoundProcessorRecovery _) → LeftD fakeErr
                   (RoundProcessorNormal rm)  → RightD rm
  abstract
    getEmRm-ed-abs : EpochManager → EitherD ErrLog RoundManager
    getEmRm-ed-abs = getEmRm-ed

    getEmRm-ed-abs≡ : getEmRm-ed-abs ≡ getEmRm-ed
    getEmRm-ed-abs≡ = refl

    getEmRm-e-abs : EpochManager → Either ErrLog RoundManager
    getEmRm-e-abs = toEither ∘ getEmRm-ed-abs


  postulate -- TODO
   getEMRM≡
    : ∀ {em : EpochManager}
    → getEmRm-e-abs em ≡ EitherD-run (getEmRm-ed-abs em)

  -- This version is currently unused, as we define the Either version below in terms of the EitherD
  -- version by using EitherD-run.  It's question of judgement whether we're OK with considering
  -- that the Either version defined this way is sufficiently obviously equivalent to the Haskell
  -- code we're modeling.
  initRMWithOutput-e-unused : BootstrapInfo → ValidatorSigner → Either ErrLog (RoundManager × List Output)
  initRMWithOutput-e-unused bsi vs = do
    (em , lo) ← initEMWithOutput-e-abs bsi vs
    rm        ← getEmRm-e-abs em
    Right (rm , lo)

  module initRMWithOutput-ed (bsi : BootstrapInfo) (vs : ValidatorSigner) where
    step₀ : EitherD ErrLog (RoundManager × List Output)
    step₁ : _ → EitherD ErrLog (RoundManager × List Output)

    step₀ = do
      (em , lo) ← initEMWithOutput-ed-abs bsi vs
      step₁ (em , lo)

    step₁ (em , lo) = do
      rm        ← getEmRm-ed-abs em
      RightD (rm , lo)

  abstract
    initRMWithOutput-e-abs : BootstrapInfo → ValidatorSigner
                           → Either ErrLog (RoundManager × List Output)
    -- Avoids duplication, but eliminates version that looks exactly like the Haskell
    initRMWithOutput-e-abs bsi vs = toEither $ initRMWithOutput-ed.step₀ bsi vs

    initRMWithOutput-ed-abs  = initRMWithOutput-ed.step₀
    initRMWithOutput-ed-abs≡ : initRMWithOutput-ed-abs ≡ initRMWithOutput-ed.step₀
    initRMWithOutput-ed-abs≡ = refl

    initRMWithOutput≡
      : ∀ {bsi : BootstrapInfo} {vs : ValidatorSigner}
      → initRMWithOutput-e-abs bsi vs ≡ EitherD-run (initRMWithOutput-ed-abs bsi vs)
    initRMWithOutput≡ {bsi} {vs} = refl

  initHandler : Author → BootstrapInfo → Maybe (RoundManager × List (LYT.Action NetworkMsg))
  initHandler pid bsi =
   case ValidatorSigner.obmGetValidatorSigner pid (bsi ^∙ bsiVSS) of λ where
     (Left _)   → nothing
     (Right vs) →
       case initRMWithOutput-e-abs bsi vs of λ where
         (Left _)          → nothing
         (Right (rm , lo)) → just (rm , outputsToActions {State = rm} lo)

  InitAndHandlers : SystemInitAndHandlers ℓ-RoundManager ConcSysParms
  InitAndHandlers =
    mkSysInitAndHandlers
      fakeBootstrapInfo
      fakeInitRM
      initHandler
      peerStep
   where
    postulate -- TODO-1: eliminate by constructing inhabitants
      bs : BlockStore
      pe : ProposerElection
      rs : RoundState
      sr : SafetyRules
      vv : BootstrapInfo → ValidatorVerifier
    -- For uninitialised peers, so we know nothing about their state.
    -- Construct a value of type `RoundManager` to ensure it is inhabitable.
    fakeInitRM : RoundManager
    fakeInitRM = RoundManager∙new
      ObmNeedFetch∙new
      (EpochState∙new 1 (vv fakeBootstrapInfo))
      bs rs pe proposalGenerator sr false
