open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types

module LibraBFT.Abstract.Records.Extends
  -- A Hash function maps a bytestring into a hash.
  (hash     : ByteString → Hash)
  -- And is colission resistant
  (hash-cr  : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec : EpochConfig) 
 where
  
  open        WithCryptoHash                        hash hash-cr
  open import LibraBFT.Abstract.Records ec  

  HashR : Record → Hash
  HashR = hash ∘ encodeR

  -- Most of the conditions in section 4.2 are ...
  -- Only round numbers and hashes are actually critical to
  -- thm S5!
  -- warn of possible changes needed in the future?!
  data _←_ : Record → Record → Set where
    I←B : {i : Initial} {b : Block}
        → 1 ≤ getRound b
        → HashR (I i) ≡ getPrevHash b
        → I i ← B b
    Q←B : {q : QC} {b : Block}
        → getRound q < getRound b
        → HashR (Q q) ≡ getPrevHash b
        → Q q ← B b
    B←Q : {b : Block} {q : QC}
        → getRound q ≡ getRound b
        → HashR (B b) ≡ getPrevHash q
        → B b ← Q q
    -- B←V : {b : Block} {v : Vote}
    --       → HashR (B b) ≡ vBlockHash v
    --       → B b ← V v

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
            → HashBroke ⊎ (r₀ ≡ r₁)
  lemmaS1-2 {i₀} {i₁} {b} (I←B _ i₀←b) (I←B _ i₁←b)
    with hash-cr (trans i₀←b (sym i₁←b))
  ... | inj₁ (i₀≢i₁ , hi₀≡hi₁) = inj₁ ( ( encodeR i₀ , encodeR i₁ ) , ( i₀≢i₁ , hi₀≡hi₁ ) )
  ... | inj₂ i₀≡i₁             = inj₂ (encodeR-inj i₀≡i₁)
  lemmaS1-2 {i} {q} {b} (I←B _ i←b) (Q←B _ q←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ ()
  lemmaS1-2 {q} {i} {b} (Q←B _ q←b) (I←B _ i←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ ()
  lemmaS1-2 {q₀} {q₁} {b} (Q←B _ q₀←b) (Q←B _ q₁←b)
     with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ (q₀≢q₁ , hq₀≡hq₁) = inj₁ ( ( encodeR q₀ , encodeR q₁ ) , ( q₀≢q₁ , hq₀≡hq₁ ) )
  ... | inj₂ q₁≡q₂             = inj₂ (encodeR-inj q₁≡q₂)
  lemmaS1-2 {b₀} {b₁} {q} (B←Q _ b₀←q) (B←Q _ b₁←q)
     with hash-cr (trans b₀←q (sym b₁←q))
  ... | inj₁ (b₀≢b₁ , hb₀←hb₁) = inj₁ ( ( encodeR b₀ , encodeR b₁ ), ( b₀≢b₁ , hb₀←hb₁ ) )
  ... | inj₂ b₀≡b₁             = inj₂ (encodeR-inj b₀≡b₁)
  -- lemmaS1-2 {b₀} {b₁} {v} (B←V b₀←v) (B←V b₁←v)
  --    with hash-cr (trans b₀←v (sym b₁←v))
  -- ... | inj₁ (b₀≢b₁ , hb₀←hb₁) = inj₁ ( (encodeR b₀ , encodeR b₁ ) , ( b₀≢b₁ , hb₀←hb₁ ) )
  -- ... | inj₂ b₀≡b₁             = inj₂ (encodeR-inj b₀≡b₁)

  -- Better name for our lemma
  ←-inj : ∀{r₀ r₁ r₂}
        → r₀ ← r₂ → r₁ ← r₂
        → HashBroke ⊎ (r₀ ≡ r₁)
  ←-inj = lemmaS1-2

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
            → HashBroke ⊎ r₀ ←⋆ r₁
  lemmaS1-3 ssRefl ssRefl rr₀<rr₁ = inj₂ ssRefl
  lemmaS1-3 ssRefl (ssStep r₁←⋆r r←r₀) rr₀<rr₁
    = contradiction (←⋆-round-< (ssStep r₁←⋆r r←r₀)) (<⇒≱ rr₀<rr₁)
  lemmaS1-3 (ssStep r₀←⋆r r←r₁) ssRefl rr₀<rr₁ 
    = inj₂ (ssStep r₀←⋆r r←r₁)
  lemmaS1-3 (ssStep r₀←⋆r r←r₂) (ssStep r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with ←-inj r←r₂ rₓ←r₂
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ refl = lemmaS1-3 r₀←⋆r r₁←⋆rₓ rr₀<rr₁

