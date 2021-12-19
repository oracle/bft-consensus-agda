{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Abstract.Types.EpochConfig
open import LibraBFT.Prelude
open        WithAbsVote

-- This module provides a convenient way for modules in other namespaces to import
-- everything from Abstract.

module LibraBFT.Abstract.Abstract
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (NodeId : Set)
  (𝓔  : EpochConfig UID NodeId)
  (𝓥  : VoteEvidence UID NodeId 𝓔)
  where
    open import LibraBFT.Abstract.Types                   UID        NodeId 𝓔    public
    open import LibraBFT.Abstract.RecordChain             UID _≟UID_ NodeId 𝓔 𝓥 public
    open import LibraBFT.Abstract.RecordChain.Assumptions UID _≟UID_ NodeId 𝓔 𝓥 public
    open import LibraBFT.Abstract.Records                 UID _≟UID_ NodeId 𝓔 𝓥 public
    open import LibraBFT.Abstract.Records.Extends         UID _≟UID_ NodeId 𝓔 𝓥 public
    open import LibraBFT.Abstract.Properties              UID _≟UID_ NodeId 𝓔 𝓥 public
    open import LibraBFT.Abstract.System                  UID _≟UID_ NodeId 𝓔 𝓥 public
