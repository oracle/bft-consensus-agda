{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules as SafetyRules
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage   as MockStorage
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.MetricsSafetyRules where

module performInitialize
  (self : SafetyRules)
  (obmPersistentLivenessStorage : PersistentLivenessStorage)
  where

  step₀ : EitherD ErrLog SafetyRules
  step₁ : EpochChangeProof → EitherD ErrLog SafetyRules

  step₀ = do
    let consensusState = SafetyRules.consensusState self
        srWaypoint     = consensusState ^∙ csWaypoint
    proofs             ← MockStorage.retrieveEpochChangeProofED
                           (srWaypoint ^∙ wVersion) obmPersistentLivenessStorage
    step₁ proofs
  step₁ proofs = SafetyRules.initialize-ed-abs self proofs

abstract
  performInitialize-ed-abs = performInitialize.step₀
  performInitialize-abs : SafetyRules → PersistentLivenessStorage → Either ErrLog SafetyRules
  performInitialize-abs sr storage = toEither $ performInitialize-ed-abs sr storage
  performInitialize-abs-≡ : (sr : SafetyRules) (storage : PersistentLivenessStorage)
                          → performInitialize-abs sr storage ≡ EitherD-run (performInitialize-ed-abs sr storage)
  performInitialize-abs-≡ sr storage = refl
