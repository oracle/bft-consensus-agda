{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
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
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.Hash
open import Util.Lemmas
open import Util.PKCS
open import Util.Prelude
open import Util.Types
open import Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

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
            → sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ nothing
            → BlockStoreInv (bs , ecInfo)
            → RoundManagerInv (initProcessor sr bs)
  initRMInv {sr} vvCorr sdInv refl bsInv = mkRoundManagerInv vvCorr refl bsInv (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))

  contract-continue2 :
      ∀ {sr bs}
    → ValidatorVerifier-correct (epochState0 ^∙ esVerifier)
    → SafetyRulesInv sr
    → sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ nothing
    → BlockStoreInv (bs , ecInfo)
    → EitherD-weakestPre (continue2-abs lastVote bs sr) (InitContract lastVote)
  contract-continue2 {sr} {bs} vvCorr srInv lvNothing bsInv rewrite continue2-abs-≡
    with LBFT-contract (RoundManager.start-abs now lastVote)
                       (Contract initRM initRMCorr)
                       (initProcessor sr bs)
                       (contract' initRM initRMCorr)
      where
        open startSpec now lastVote
        initRM     = initProcessor sr bs
        initRMCorr = initRMInv {sr} {bs} vvCorr (sdInv srInv) lvNothing bsInv

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
     with emiSRI emi R
  ...| (sri , lvNothing)
     with performInitializeSpec.contract safetyRules (self0 ^∙ emStorage) sri lvNothing
  ...| piProp
     with MetricsSafetyRules.performInitialize-abs safetyRules (self0 ^∙ emStorage)
  ...| Left _ = tt
  ...| Right sr = contract-continue2 vvCorr (performInitializeSpec.ContractOk.srPres    piProp sri)
                                            (performInitializeSpec.ContractOk.lvNothing piProp) bsInv

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
