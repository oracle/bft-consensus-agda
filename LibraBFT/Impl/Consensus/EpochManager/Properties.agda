{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

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
open import LibraBFT.Impl.Consensus.EpochManager                       as EpochManager
import      LibraBFT.Impl.Consensus.MetricsSafetyRules                 as MetricsSafetyRules
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

module LibraBFT.Impl.Consensus.EpochManager.Properties where

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
  initProcessor : SafetyRules → BlockStore → RoundManager
  initProcessor sr bs =
    RoundManager∙new
      obmNeedFetch
      epochState0
      bs
      roundState
      proposerElection
      proposalGenerator
      (sr & srPersistentStorage ∙ pssSafetyData ∙ sdEpoch ∙~ epochState0 ^∙ esEpoch)
      (self0 ^∙ emConfig ∙ ccSyncOnly)

  module SS
    where open startSpec now lastVote public

  contract-continue2
    : ∀ sr bs
    → EitherD-weakestPre (continue2-abs lastVote bs sr) InitContract
  contract-continue2 sr bs rewrite continue2-abs-≡
    with LBFT-contract (RoundManager.start-abs now lastVote)
                       (SS.Contract (initProcessor sr bs) unit)
                       (initProcessor sr bs)
                       (SS.contract' (initProcessor sr bs) unit)
  ...| inj₁ (_    , er≡j ) rewrite er≡j = tt
  ...| inj₂ (er≡n , ico) rewrite er≡n =
         LBFT-post (RoundManager.start-abs now lastVote)
                   (initProcessor sr bs)
         , refl , ico

  contract-continue1
    : ∀ bs
    → EitherD-weakestPre (continue1-abs (recoveryData ^∙ rdLastVote) bs) InitContract
  contract-continue1 bs rewrite continue1-abs-≡
     with MetricsSafetyRules.performInitialize-abs
            (SafetyRulesManager.client-abs (self0 ^∙ emSafetyRulesManager))
            (self0 ^∙ emStorage)
  ...| Left _ = tt
  ...| Right sr = contract-continue2 sr bs

  contract' : EitherD-weakestPre
                (EpochManager.startRoundManager'-ed-abs
                   self0 now recoveryData epochState0
                   obmNeedFetch obmProposalGenerator obmVersion)
              InitContract
  contract' rewrite startRoundManager'-ed-abs-≡
     with BlockStore.new-e-abs (self0 ^∙ emStorage) recoveryData stateComputer
                               (self0 ^∙ emConfig ∙ ccMaxPrunedBlocksInMem)
  ...| Left  _  = tt
  ...| Right bs = contract-continue1 bs
