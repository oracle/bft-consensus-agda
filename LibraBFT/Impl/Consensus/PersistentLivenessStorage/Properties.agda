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
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs

module LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties where

module saveVoteMSpec (vote : Vote) where
  open OutputProps
  -- TODO-2: This contract needs refining (after `saveVoteM` is implemented)
  postulate
    contract
      : ∀ P pre
        → (∀ outs → NoMsgs outs → NoErrors outs → P (inj₁ fakeErr) pre outs)
        → (∀ outs → NoMsgs outs → NoErrors outs
           → P (inj₂ unit) pre outs)
        → RWST-weakestPre (saveVoteM vote) P unit pre
