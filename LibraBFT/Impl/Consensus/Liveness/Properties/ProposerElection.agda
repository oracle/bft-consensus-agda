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
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection

module LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection where

module IsValidProposalM (b : Block) where
  postulate
    contract
      : ∀ P pre
        → (∀ b → P b pre [])
        → RWST-weakestPre (isValidProposalM b) P unit pre
