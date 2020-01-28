open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.Records.Extends
  (ec : EpochConfig) (UID : B∨QC → Set)
 where
  
  open import LibraBFT.Abstract.Records ec UID

  -- Most of the conditions in section 4.2 are ...
  -- Only round numbers and hashes are actually critical to
  -- thm S5!
  -- warn of possible changes needed in the future?!
  data _←_ : Record → Record → Set where
    I←B : {b : Block}
        → 1 ≤ getRound b
        → bPrev b ≡ nothing
        → I ← B b
    Q←B : {q : QC} {b : Block}
        → getRound q < getRound b
        → just (qId q) ≡ bPrev b
        → Q q ← B b
    B←Q : {b : Block} {q : QC}
        → getRound q ≡ getRound b
        → bId b ≡ qPrev q
        → B b ← Q q

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

  -- LemmaS1, clause 2: injectivity of _←_
  lemmaS1-2 : ∀{r₀ r₁ r₂}
            → r₀ ← r₂ → r₁ ← r₂
            → uid r₀ ≡ uid r₁
  lemmaS1-2 {i₀} {i₁} {b} (I←B _ i₀←b) (I←B _ i₁←b) = refl
  lemmaS1-2 {q} {i} {b} (Q←B _ ()) (I←B _ refl) 
  lemmaS1-2 {i} {q} {b} (I←B _ refl) (Q←B _ ())
  lemmaS1-2 {q₀} {q₁} {b} (Q←B _ refl) (Q←B _ refl) = refl
  lemmaS1-2 {b₀} {b₁} {q} (B←Q _ refl) (B←Q _ refl) = refl

  -- Better name for our lemma
  ←-inj : ∀{r₀ r₁ r₂}
        → r₀ ← r₂ → r₁ ← r₂
        → uid r₀ ≡ uid r₁
  ←-inj = lemmaS1-2

{-
  -----------------------------------------
  -- Reflexive-Transitive Closure of _←_ --
  -----------------------------------------

  -- This is the reflexive-transitive closure of _←_, as defined in 
  -- section 4.7 in the paper. 
  data _←⋆_ (r₁ : Record) : Record → Set₁ where
    ssRefl : r₁ ←⋆ r₁
    ssStep : ∀ {r r₂ : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂

  ←⋆-round-< : ∀{r₀ r₁}
             → r₀ ←⋆ r₁
             → round r₀ ≤ round r₁
  ←⋆-round-< ssRefl         = ≤-refl
  ←⋆-round-< (ssStep ext x) = ≤-trans (←⋆-round-< ext) (←-round-≤ x)

  -- Lemma S1, clause 3
  lemmaS1-3 : ∀{r₀ r₁ r₂}
            → r₀ ←⋆ r₂ → r₁ ←⋆ r₂
            → round r₀ < round r₁
            → r₀ ←⋆ r₁
  lemmaS1-3 ssRefl ssRefl rr₀<rr₁ = ssRefl
  lemmaS1-3 ssRefl (ssStep r₁←⋆r r←r₀) rr₀<rr₁
    = contradiction (←⋆-round-< (ssStep r₁←⋆r r←r₀)) (<⇒≱ rr₀<rr₁)
  lemmaS1-3 (ssStep r₀←⋆r r←r₁) ssRefl rr₀<rr₁ 
    = ssStep r₀←⋆r r←r₁
  lemmaS1-3 (ssStep r₀←⋆r r←r₂) (ssStep r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with ←-inj r←r₂ rₓ←r₂
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ refl = lemmaS1-3 r₀←⋆r r₁←⋆rₓ rr₀<rr₁
-}

