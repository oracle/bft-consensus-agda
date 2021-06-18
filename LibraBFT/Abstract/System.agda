{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Abstract.Types.EpochConfig
open import LibraBFT.Prelude
open WithAbsVote

-- This module defines and abstract view if a system, encompassing only a predicate for Records,
-- another for Votes and a proof that, if a Vote is included in a QC in the system, then and
-- equivalent Vote is also in the system.  It further defines a notion "Complete", which states that
-- if an honest vote is included in a QC in the system, then there is a RecordChain up to the block
-- that the QC extends, such that all Records in the RecordChain are also in the system.  The latter
-- property is used to extend correctness conditions on RecordChains to correctness conditions that
-- require only a short suffix of a RecordChain.

module LibraBFT.Abstract.System
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (NodeId : Set)
    (𝓔 : EpochConfig UID NodeId)
    (𝓥 : VoteEvidence UID NodeId 𝓔)
  where

  open import LibraBFT.Abstract.Types           UID        NodeId 𝓔
  open import LibraBFT.Abstract.Records         UID _≟UID_ NodeId 𝓔 𝓥
  open import LibraBFT.Abstract.Records.Extends UID _≟UID_ NodeId 𝓔 𝓥
  open import LibraBFT.Abstract.RecordChain     UID _≟UID_ NodeId 𝓔 𝓥

  module All-InSys-props {ℓ}(InSys : Record → Set ℓ) where

    All-InSys : ∀ {o r} → RecordChainFrom o r → Set ℓ
    All-InSys rc = {r' : Record} → r' ∈RC-simple rc → InSys r'

    All-InSys⇒last-InSys : ∀ {r} → {rc : RecordChain r} → All-InSys rc → InSys r
    All-InSys⇒last-InSys {rc = empty} a∈s = a∈s here
    All-InSys⇒last-InSys {r = r'} {step {r' = .r'} rc ext} a∈s = a∈s here

    All-InSys-unstep : ∀ {o r r' rc ext } → All-InSys (step {o} {r} {r'} rc ext) → All-InSys rc
    All-InSys-unstep {ext = ext} a∈s r'∈RC = a∈s (there ext r'∈RC)

    All-InSys-step : ∀ {r r' }{rc : RecordChain r}
                   → All-InSys rc → (ext : r ← r') → InSys r'
                   → All-InSys (step rc ext)
    All-InSys-step hyp ext r here = r
    All-InSys-step hyp ext r (there .ext r∈rc) = hyp r∈rc

  -- We say an InSys predicate is /Complete/ when we can construct a record chain
  -- from any vote by an honest participant. This essentially says that whenever
  -- an honest participant casts a vote, they have checked that the voted-for
  -- block is in a RecordChain whose records are all in the system.  This notion
  -- is used to extend correctness conditions on RecordChains to correctness conditions that
  -- require only a short suffix of a RecordChain.
  Complete : ∀{ℓ} → (Record → Set ℓ) → Set ℓ
  Complete ∈sys = ∀{α q}
                → Meta-Honest-Member α
                → α ∈QC q
                → ∈sys (Q q)
                → ∃[ b ] ( Σ (RecordChain (B b)) All-InSys
                         × B b ← Q q)
    where open All-InSys-props ∈sys
