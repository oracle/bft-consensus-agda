{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
-- import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore       as BlockStore
-- import      LibraBFT.Impl.Consensus.BlockStorage.BlockStoreSpec   as BlockStoreSpec
-- import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock  as ExecutedBlock
-- import      LibraBFT.Impl.Consensus.Liveness.ProposerElection     as ProposerElection
-- import      LibraBFT.Impl.Consensus.PersistentLivenessStorage     as PersistentLivenessStorage
-- import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules       as SafetyRules
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.RoundManager.PropertyDefs where

-- The codomain for the property that a vote has been correctly tagged with the
-- source meta-data. The actual statement of the property depends on the
-- stateful computation we are considering (e.g., whether the vote is being
-- returned or emitted as output).
VoteSrcCorrectCod : (pre post : RoundManager) → VoteWithMeta → Set
VoteSrcCorrectCod pre post (VoteWithMeta∙new vote mvsNew) =
  just vote ≡ post ^∙ lSafetyData ∙ sdLastVote
VoteSrcCorrectCod pre post (VoteWithMeta∙new vote mvsLastVote) =
  just vote ≡ pre ^∙ lSafetyData ∙ sdLastVote
