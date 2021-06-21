{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage

module LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties where

open RWST-do

module SaveVoteM (vote : Vote) where
  -- TODO-2: Prove this (after implementing `saveVoteM`)
  postulate
    contract
      : ∀ P pre
        → P (inj₁ fakeErr) pre []
        → (∀ blockStore → P (inj₂ unit) (rmSetBlockStore pre blockStore) [])
        → RWST-weakestPre (saveVoteM vote) P unit pre
