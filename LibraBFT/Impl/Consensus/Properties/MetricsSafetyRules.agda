open import LibraBFT.Impl.Consensus.MetricsSafetyRules
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude                               hiding (_++_)
open import Optics.All

module LibraBFT.Impl.Consensus.Properties.MetricsSafetyRules where

open Invariants

module performInitializeSpec
  (safetyRules : SafetyRules)
  (storage     : PersistentLivenessStorage)
  where

  record ContractOk (sr : SafetyRules) : Set where
    constructor mkContractOk
    field
      srPres    : Preserves SafetyRulesInv safetyRules sr
      lvNothing : sr ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ nothing
  open ContractOk

  Contract : EitherD-Post ErrLog SafetyRules
  Contract (Left _)   = ⊤
  Contract (Right sr) = ContractOk sr

  module _ (sri : SafetyRulesInv safetyRules)
           (lvNothing : safetyRules ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote ≡ nothing)
    where
    -- TODO-2: Requires refinement
    postulate
     contract' : EitherD-weakestPre (performInitialize-ed-abs safetyRules storage) Contract

    contract : Contract (performInitialize-abs safetyRules storage)
    contract rewrite performInitialize-abs-≡ safetyRules storage =
      EitherD-contract (performInitialize-ed-abs safetyRules storage) Contract contract'
