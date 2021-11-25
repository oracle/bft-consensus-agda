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

  Contract : EitherD-Post ErrLog SafetyRules
  Contract (Left _)   = ⊤
  Contract (Right sr) = SafetyRulesInv sr

  module _ (sri : SafetyRulesInv safetyRules) where
    -- TODO-2: Requires refinement
    postulate
     contract' : EitherD-weakestPre (performInitialize-ed-abs safetyRules storage) Contract

    contract : Contract (performInitialize-abs safetyRules storage)
    contract rewrite performInitialize-abs-≡ safetyRules storage =
      EitherD-contract (performInitialize-ed-abs safetyRules storage) Contract contract'
