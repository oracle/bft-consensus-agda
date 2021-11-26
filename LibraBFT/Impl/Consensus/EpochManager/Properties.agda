{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore            as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore as BSprops
open import LibraBFT.Impl.Consensus.EpochManager                       as EpochManager
import      LibraBFT.Impl.Consensus.MetricsSafetyRules                 as MetricsSafetyRules
open import LibraBFT.Impl.Consensus.Properties.MetricsSafetyRules
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRulesManager     as SafetyRulesManager
import      LibraBFT.Impl.Consensus.RoundManager                       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open InitProofDefs
open Invariants
open EpochManagerInv
open SafetyRulesInv
open SafetyDataInv

module LibraBFT.Impl.Consensus.EpochManager.Properties where

module newSpec
  (nodeConfig                : NodeConfig)
  (stateComp                 : StateComputer)
  (persistentLivenessStorage : PersistentLivenessStorage)
  (obmAuthor                 : Author)
  (obmSK                     : SK)
  where

  -- TODO-2: May require refinement (additional requirements and/or properties)
  Contract : EitherD-Post ErrLog EpochManager
  Contract (Left _)   = ⊤
  Contract (Right em) = ∀ {sr} → em ^∙ emSafetyRulesManager ∙ srmInternalSafetyRules ≡ SRWLocal sr
                               → sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ nothing

  postulate
    contract : Contract (EpochManager.new nodeConfig stateComp persistentLivenessStorage obmAuthor obmSK)

module startRoundManager'Spec
  (self0                : EpochManager)
  (now                  : Instant)
  (recoveryData         : RecoveryData)
  (epochState0          : EpochState)
  (obmNeedFetch         : ObmNeedFetch)
  (obmProposalGenerator : ProposalGenerator)
  (obmVersion           : Version)
  where

  open startRoundManager'-ed self0 now recoveryData epochState0
                             obmNeedFetch obmProposalGenerator obmVersion

  lastVote = recoveryData ^∙ rdLastVote
  proposalGenerator = obmProposalGenerator
  roundState = createRoundState-abs self0 now
  proposerElection = createProposerElection epochState0
  srUpdate : SafetyRules → SafetyRules
  srUpdate  = _& srPersistentStorage ∙ pssSafetyData ∙ sdEpoch ∙~ epochState0 ^∙ esEpoch
  initProcessor : SafetyRules → BlockStore → RoundManager
  initProcessor sr bs =
    RoundManager∙new
      obmNeedFetch
      epochState0
      bs
      roundState
      proposerElection
      proposalGenerator
      (srUpdate sr)
      (self0 ^∙ emConfig ∙ ccSyncOnly)

  ecInfo = mkECinfo (epochState0 ^∙ esVerifier) (epochState0 ^∙ esEpoch)

  SRVoteEpoch≡ : SafetyRules → Epoch → Set
  SRVoteEpoch≡ sr epoch = ∀ {v} → sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ just v
                                → v ^∙ vEpoch ≡ epoch

  SRVoteRound≤ : SafetyRules → Set
  SRVoteRound≤ sr = let sd = sr ^∙ srPersistentStorage ∙ pssSafetyData
                     in Meta.getLastVoteRound sd ≤ sd ^∙ sdLastVotedRound

  initRMInv : ∀ {sr bs}
            → ValidatorVerifier-correct (epochState0 ^∙ esVerifier)
            → SafetyDataInv (sr ^∙ srPersistentStorage ∙ pssSafetyData)
            → BlockStoreInv (bs , ecInfo)
            → RoundManagerInv (initProcessor sr bs)
  initRMInv {sr} vvCorr sdInv bsInv
     with sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote | inspect
          (sr ^∙_) (srPersistentStorage ∙ pssSafetyData ∙ sdLastVote)
  ...| nothing | _ = mkRoundManagerInv vvCorr refl bsInv (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))
  ...| just v  | [ refl ] = mkRoundManagerInv vvCorr refl bsInv
                  (mkSafetyRulesInv (subst-SafetyDataInv {sr ^∙ srPersistentStorage ∙ pssSafetyData}
                                                         {srUpdate sr ^∙ srPersistentStorage ∙ pssSafetyData}
                                                         refl
                                                         (obm-dangerous-magic' "DANGER - READ COMMENT BELOW")
                                                         refl sdInv))

{- Here we run into an issue that may reflect an implementation bug.  Alternatively, it may be that
  one of our invariants (specifically SafetyDataInv) is too strong.  The following "essay" captures
  my thinking, but writing this helped me reach a tentative conclusion, summarised at the bottom.

  Attempting to give `refl` (instead of obm-dangerous-magic') above reveals the issue: at line 289
  in EpochManager.agda and reflected at lines 87 and 77 above), startRoundManager sets sdEpoch of
  safetyRules to epochState0 ^∙ esEpoch.  However, startRoundManager does NOT change sdLastVote.
  Therefore, it is possible that, by setting sdEpoch, startRoundManager falsifies the lvEpoch≡ field
  of SafetyDataInv.

  Let's examine the circumstances under which this might occur.

  This safetyRules has been acquired by looking up a SafetyRules in the epochManager (lines
  268-269 in RoundManager), which presumably should satisfy SafetyRulesInv, and then passing this
  to performInitialize (line 270), which in turn passes it to SafetyRules.initialize-ed-abs (line
  31 in MetricSafetyRules); initialize-ed-abs is a proxy for an EitherD version of initialize,
  which has not yet been converted to EitherD.

  initialize constructs an EpochState (lines 166-172 in SafetyRules), and then compares its epoch
  to the current epoch, taken from sdEpoch (lines 173-174).  In the typical epoch change
  scenario, in which the peer is moving to a higher epoch, the SafetyRules to be passed to
  continue2 is constructed with a nothing for sdLastVote.  In this case, by the definition of
  Meta.getLastVoteEpoch, the lvEpoch≡ requirement holds trivially.  Similarly,
  Meta.getLastVoteRound is 0 in this case, so the lvRound≤ requirement can be easily satisfied
  with z≤n (see line 108 above).

  However, in case the constructed epochState is for an epoch that is not greater than the peer's
  current epoch, the SafetyRules received by initialize is passed unmodified to continue1.  The
  rest of startRoundManager (continue1 and continue2) does not modify sdLastVote.  Thus,
  performInitialize may return a SafetyRules whose sdLastVote ≡ just v for some v.  This
  SafetyRules is the one passed to continue2 (line 272 in EpochManager).

  continue2 then constructs a new RoundManager, providing the SafetyRules component by MODIFYING
  sdEpoch in the returned SafetyRules, setting it to epochState0 ^∙ esEpoch (line 289).  It seems
  clear that epochState0 ^∙ esEpoch differs from the existing sdEpoch, and sdLastVote is just v,
  then this change falsifies the lvEpoch≡ field of sdInv.

  This new RoundManager is passed to RoundManager.start (line 293).

  Some possibilities to consider:

  1.  It doesn't matter that the invariant (as currently stated) does not hold at this point.
      This could be because:

      1a. it gets restored somewhere downstream before any damage occurs, or

      1b. no damage will occur (e.g, perhaps when considering whether to vote, we will check
      sdLastVote, find that it is for the wrong epoch, and bail out or repair the invariant first)

  2.  It does matter.  Some possibilities:

      2a. We could change the code to ensure the invariant (as currently stated) is not falsified.
          I think this could be acheived by setting sdLastVote to nothing in the case in which line
          289 CHANGES sdEpoch (it is probably important NOT to set sdLastVote to nothing if line 289
          happens to overwrite the SAME value to sdEpoch)

      2b. We could confirm that we are in case 1, or possibly change the code to make sure we are.
          In this case, we will need to weaken the invariant so that we can prove it.  It might be
          that changing SafetyDataInv to be something like:

             Meta.getLastVoteEpoch sd ≡ sd ^∙ sdEpoch
           → Meta.getLastVoteRound sd ≤ sd ^∙ sdLastVotedRound

          in case we confirm/ensure that we are in case 1b.

      2c. It could be that the implementation maintains an invariant that sdLastVote of the
          SafetyData within the EpochManager's SafetyRulesManager is always nothing.  This is the
          case for the INITIAL EpochManager, constructed using EpochManager.new (see line 42 in
          SafetyRules, which is reached 

  In any case, we need to understand more detail to determine what to do.  I have written the above
  to facilitate discussion.

  One thing to note is that for the first epoch, sdLastVote is nothing (startConsensus ->
  startForTesting -> MockSharedStorage.new*; see MockSharedStorage, line 19).  Therefore, we could
  prove a weaker version of startRoundManagerSpec.contract', which assumes that sdLastVote is
  nothing, and this would suffice for continuing our current work on proving safety for the first
  epoch.

  TENTATIVE CONCLUSION

  Writing the last paragraph above caused me to challenge my assumption that sdLastVote in the
  SafetyRules obtained from the EpochManager's SafetyRulesManager might not be `nothing`.  In
  particular, it seems that when we start a new epoch we ensure that it IS `nothing` (startNewEpoch
  -> expectNewEpoch -> startProcessor -> startForTesting -> MockSharedStorage.new*; see
  MockSharedStorage, line 19); note that the EpochManager returned by startProcessor is the one
  provided to the PMNewEpochManager constructed by expectNewEpoch).  Therefore, I plan to strengthen
  the initial EpochManager invariant accordingly.

-}

  contract-continue2 :
      ∀ {sr bs}
    → ValidatorVerifier-correct (epochState0 ^∙ esVerifier)
    → SafetyRulesInv sr
    → BlockStoreInv (bs , ecInfo)
    → EitherD-weakestPre (continue2-abs lastVote bs sr) (InitContract lastVote)
  contract-continue2 {sr} {bs} vvCorr srInv bsInv rewrite continue2-abs-≡
    with LBFT-contract (RoundManager.start-abs now lastVote)
                       (Contract initRM initRMCorr)
                       (initProcessor sr bs)
                       (contract' initRM initRMCorr)
      where
        open startSpec now lastVote
        initRM     = initProcessor sr bs
        initRMCorr = initRMInv {sr} {bs} vvCorr (sdInv srInv) bsInv

  ...| inj₁ (_    , er≡j ) rewrite er≡j = tt
  ...| inj₂ (er≡n , ico) rewrite er≡n =
         LBFT-post (RoundManager.start-abs now lastVote)
                   (initProcessor sr bs)
         , refl , ico

  contract-continue1
    : ∀ {bs}
    → BlockStoreInv (bs , ecInfo)
    → ValidatorVerifier-correct (epochState0 ^∙ esVerifier)
    → EpochManagerInv self0
    → EitherD-weakestPre (continue1-abs lastVote bs) (InitContract lastVote)
  contract-continue1 {bs} bsInv vvCorr emi rewrite continue1-abs-≡
     with  self0 ^∙    emSafetyRulesManager ∙ srmInternalSafetyRules | inspect
          (self0 ^∙_) (emSafetyRulesManager ∙ srmInternalSafetyRules) 
  ...| SRWLocal safetyRules | [ R ]
     with performInitializeSpec.contract safetyRules (self0 ^∙ emStorage) (emiSRI emi R)
  ...| piProp
     with MetricsSafetyRules.performInitialize-abs safetyRules (self0 ^∙ emStorage)
  ...| Left _ = tt
  ...| Right sr = contract-continue2 vvCorr piProp bsInv

  contract' :
      ValidatorVerifier-correct (epochState0 ^∙ esVerifier)
    → EpochManagerInv self0
    → EitherD-weakestPre
                (EpochManager.startRoundManager'-ed-abs
                   self0 now recoveryData epochState0
                   obmNeedFetch obmProposalGenerator obmVersion)
              (InitContract lastVote)
  contract' vvCorr emi rewrite startRoundManager'-ed-abs-≡
     with BSprops.new.contract (self0 ^∙ emStorage) recoveryData stateComputer
                               (self0 ^∙ emConfig ∙ ccMaxPrunedBlocksInMem)
  ...| bsprop
     with BlockStore.new-e-abs (self0 ^∙ emStorage) recoveryData stateComputer
                               (self0 ^∙ emConfig ∙ ccMaxPrunedBlocksInMem)
  ...| Left  _  = tt
  ...| Right bs = contract-continue1 bsprop vvCorr emi
