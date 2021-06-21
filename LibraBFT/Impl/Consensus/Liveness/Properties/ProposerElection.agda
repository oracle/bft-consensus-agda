{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection

module LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection where

module IsValidProposalM (b : Block) where
  -- TODO-1: This will require performing case analysis using `with` on
  -- > getValidProposer pe (b ^∙ bRound) ≟ℕ a
  -- in the case that `just a ≡ b ^∙ bAuthor`.
  contract
    : ∀ Post pre
      → let pe = pre ^∙ lProposerElection
            ma = b ^∙ bAuthor
            r  = b ^∙ bRound in
        (ma ≡ nothing ⊎ Maybe-Any (getValidProposer pe r ≢_) ma → Post false pre [])
        → (Maybe-Any (getValidProposer pe r ≡_) ma → Post true pre [])
        → RWST-weakestPre (isValidProposalM b) Post unit pre
  contract Post pre = {!!}
