{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.VoteData where

verify : VoteData → Either ErrLog Unit
verify self = do
  lcheck (self ^∙ vdParent ∙ biEpoch == self ^∙ vdProposed ∙ biEpoch)
         ("parent and proposed epochs do not match" ∷ [])
  lcheck (⌊ self ^∙ vdParent ∙ biRound <?  self ^∙ vdProposed ∙ biRound ⌋)
         ("proposed round is less than parent round" ∷ [])
  -- lcheck (self^.vdParent.biTimestamp <= self^.vdProposed.biTimestamp)
  --       ["proposed happened before parent"]
  lcheck (⌊ (self ^∙ vdParent ∙ biVersion) ≤?-Version (self ^∙ vdProposed ∙ biVersion) ⌋)
         ("proposed version is less than parent version" ∷ [])
         -- , lsVersion (self^.vdProposed.biVersion), lsVersion (self^.vdParent.biVersion)]

new : BlockInfo → BlockInfo → VoteData
new = VoteData∙new

