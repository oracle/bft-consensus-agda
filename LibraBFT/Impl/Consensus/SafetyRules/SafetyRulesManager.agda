{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

------------------------------------------------------------------------------
open import LibraBFT.Base.PKCS
import      LibraBFT.Impl.Consensus.SafetyRules.PersistentSafetyStorage as PersistentSafetyStorage
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules             as SafetyRules
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRulesManager where

storage
  : SafetyRulesConfig -> Author -> SK
  → Either ErrLog PersistentSafetyStorage
storage config obmMe obmSK = do
  pure $ PersistentSafetyStorage.new  -- internalStorage
           obmMe
           (config ^∙ srcObmGenesisWaypoint)
           obmSK

newLocal : PersistentSafetyStorage → Bool → Either ErrLog SafetyRulesManager

new
  : SafetyRulesConfig → Author → SK
  → Either ErrLog SafetyRulesManager
new config obmMe obmSK = do
  storage0               ← storage config obmMe obmSK
  let exportConsensusKey = config ^∙ srcExportConsensusKey
  case config ^∙ srcService of λ where
    SRSLocal → newLocal storage0 exportConsensusKey

newLocal storage0 exportConsensusKey = do
  safetyRules ← SafetyRules.new storage0 exportConsensusKey
  pure (mkSafetyRulesManager (SRWLocal safetyRules))

client : SafetyRulesManager → SafetyRules
client self = case self ^∙ srmInternalSafetyRules of λ where
  (SRWLocal safetyRules) → safetyRules

abstract
  client-abs = client
  client-abs-≡ : client-abs ≡ client
  client-abs-≡ = refl
