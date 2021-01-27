{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Abstract.Types

-- This module defines and abstract view if a system, encompassing only a predicate for Records,
-- another for Votes and a proof that, if a Vote is included in a QC in the system, then and
-- equivalent Vote is also in the system.  It further defines a notion "Complete", which states that
-- if an honest vote is included in a QC in the system, then there is a RecordChain up to the block
-- that the QC extends, such that all Records in the RecordChain are also in the system.  The latter
-- property is used to extend correctness conditions on RecordChains to correctness conditions that
-- require only a short suffix of a RecordChain.

module LibraBFT.Abstract.System
    (𝓔      : EpochConfig)
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (𝓥      : VoteEvidence 𝓔 UID)
   where

  open import LibraBFT.Abstract.Records         𝓔 UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.Records.Extends 𝓔 UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.RecordChain     𝓔 UID _≟UID_ 𝓥

  -- Since the invariants we want to specify (votes-once and locked-round-rule),
  -- are predicates over a /System State/, we must factor out the necessary
  -- functionality.
  --
  -- An /AbsSystemState/ supports a few different notions; namely,
  record AbsSystemState (ℓ : Level) : Set (ℓ+1 ℓ) where
    field
      -- A notion of membership of records
      InSys : Record → Set ℓ

      -- A predicate about whether votes have been transfered
      -- amongst participants
      HasBeenSent : Vote → Set ℓ

      -- Such that, the votes that belong to honest participants inside a
      -- QC that exists in the system must have been sent
      ∈QC⇒HasBeenSent : ∀{q α} → InSys (Q q) → Meta-Honest-Member 𝓔 α
                      → (va : α ∈QC q) → HasBeenSent (∈QC-Vote q va)

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


  -- We say an /AbsSystemState/ is /Complete/ when we can construct a record chain
  -- from any vote by an honest participant. This essentially says that whenever
  -- an honest participant casts a vote, they have checked that the voted-for
  -- block is in a RecordChain whose records are all in the system.
  Complete : ∀{ℓ} → AbsSystemState ℓ → Set ℓ
  Complete sys = ∀{α q }
               → Meta-Honest-Member 𝓔 α
               → (va : α ∈QC q)
               → InSys (Q q)
               → ∃[ b ] (B b ← Q q
                         × Σ (RecordChain (B b))
                             (λ rc → All-InSys rc))
    where open AbsSystemState sys
          open All-InSys-props InSys
