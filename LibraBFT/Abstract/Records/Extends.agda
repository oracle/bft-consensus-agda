{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Abstract.Types
open import LibraBFT.Abstract.Types.EpochConfig
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open WithAbsVote

-- This module defines the notion of one Record r "extending" another
-- Record r' (denoted r' ← r), ensuring rules about rounds and that r
-- correctly identifies r'

module LibraBFT.Abstract.Records.Extends
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (NodeId : Set)
    (𝓔      : EpochConfig UID NodeId)
    (𝓥     : VoteEvidence UID NodeId 𝓔)
  where

  open import LibraBFT.Abstract.Records UID _≟UID_ NodeId 𝓔 𝓥

  -- Most of the conditions in section 4.2 of the paper (see
  -- LibraBFT.Abstract.RecordChain.Properties) would be checked
  -- by the implementation to validate data received.
  --
  -- In the Abstract model, however, we are only concerned with
  -- proving the properties; only round numbers and identifiers
  -- for previous records are actually critical to thm S5!
  data _←_ : Record → Record → Set where
    I←B : {b : Block}
        → 0 < getRound b
        → bPrevQC b ≡ nothing
        → I ← B b
    Q←B : {q : QC} {b : Block}
        → getRound q < getRound b
        → just (qCertBlockId q) ≡ bPrevQC b
        → Q q ← B b
    B←Q : {b : Block} {q : QC}
        → getRound q ≡ getRound b
        → bId b ≡ qCertBlockId q
        → B b ← Q q

  -- Equivalent records extend equivalent records (modulo injectivity
  -- failure of bId).
  ←-≈Rec : ∀{r₀ r₁ s₀ s₁} → (ext₀ : s₀ ← r₀) → (ext₁ : s₁ ← r₁)
           → r₀ ≈Rec r₁
           → NonInjective-≡-preds ((s₀ ≡_) ∘ B) ((s₁ ≡_) ∘ B) bId ⊎ (s₀ ≈Rec s₁)
  ←-≈Rec (I←B x x₁) (I←B x₂ x₃) hyp = inj₂ eq-I
  ←-≈Rec (I←B x x₁) (Q←B x₂ x₃) (eq-B refl)
    = ⊥-elim (maybe-⊥ (sym x₃) x₁)
  ←-≈Rec (Q←B x x₁) (I←B x₂ x₃) (eq-B refl)
    = ⊥-elim (maybe-⊥ (sym x₁) x₃)
  ←-≈Rec (Q←B {q₀} x refl) (Q←B {q₁} x₂ refl) (eq-B refl)
    = inj₂ (eq-Q refl) -- Here is where we wouldn't be able to
                       -- complete the proof if we required round equality
                       -- in eq-Q
  ←-≈Rec (B←Q {b₀} x refl) (B←Q {b₁} w refl) (eq-Q refl)
    with b₀ ≟Block b₁
  ...| no  hb  = inj₁ (((b₀ , b₁) , (λ x → hb x) , refl) , refl , refl)
  ...| yes prf = inj₂ (eq-B prf)

  ←-irrelevant : Irrelevant _←_
  ←-irrelevant (I←B r₁ h₁) (I←B r₂ h₂)
    = cong₂ I←B (≤-irrelevant r₁ r₂) (≡-irrelevant h₁ h₂)
  ←-irrelevant (Q←B r₁ h₁) (Q←B r₂ h₂)
    = cong₂ Q←B (≤-irrelevant r₁ r₂) (≡-irrelevant h₁ h₂)
  ←-irrelevant (B←Q r₁ h₁) (B←Q r₂ h₂)
    = cong₂ B←Q (≡-irrelevant r₁ r₂) (≡-irrelevant h₁ h₂)

  ←-round-≤ : ∀{r₀ r₁} → r₀ ← r₁ → round r₀ ≤ round r₁
  ←-round-≤ (I←B r h)    = z≤n
  ←-round-≤ (Q←B r h)    = <⇒≤ r
  ←-round-≤ (B←Q refl h) = ≤-refl

  ←←-round-< : ∀{r r₀ r₁} → r ← r₀ → r₀ ← r₁
             → round r < round r₁
  ←←-round-< (I←B r h)     (B←Q refl _) = r
  ←←-round-< (Q←B r h)     rr           = ≤-trans r (←-round-≤ rr)
  ←←-round-< (B←Q refl h)  (Q←B prf _)  = prf

  -- LemmaS1, clause 2: injectivity of _←_
  lemmaS1-2 : ∀{r₀ r₁ r₂ r₂'}
            → r₂ ≈Rec r₂'
            → r₀ ← r₂ → r₁ ← r₂'
            → uid r₀ ≡ uid r₁
  lemmaS1-2 {i₀} {i₁} {b} hyp (I←B _ i₀←b) (I←B _ i₁←b) = refl
  lemmaS1-2 {q}  {i}  {b} (eq-B refl) (Q←B _ ())   (I←B _ refl)
  lemmaS1-2 {i}  {q}  {b} (eq-B refl) (I←B _ refl) (Q←B _ ())
  lemmaS1-2 {q₀} {q₁} {b} (eq-B refl) (Q←B _ refl) (Q←B _ refl) = refl
  lemmaS1-2 {b₀} {b₁} {q} (eq-Q refl) (B←Q _ refl) (B←Q _ refl) = refl

  -- A better name for lemmaS1-2
  ←-inj : ∀{r₀ r₁ r₂}
        → r₀ ← r₂ → r₁ ← r₂
        → uid r₀ ≡ uid r₁
  ←-inj = lemmaS1-2 ≈Rec-refl
