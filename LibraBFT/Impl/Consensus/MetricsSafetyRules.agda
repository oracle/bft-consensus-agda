{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules as SafetyRules
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage   as MockStorage
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.MetricsSafetyRules where

performInitialize : SafetyRules → PersistentLivenessStorage → Either ErrLog SafetyRules
performInitialize self obmPersistentLivenessStorage = do
  let consensusState = SafetyRules.consensusState self
      srWaypoint     = consensusState ^∙ csWaypoint
  proofs            <- MockStorage.retrieveEpochChangeProofE
                         (srWaypoint ^∙ wVersion) obmPersistentLivenessStorage
  SafetyRules.initialize self proofs
