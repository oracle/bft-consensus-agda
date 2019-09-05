{-# OPTIONS --allow-unsolved-metas #-}
open import Hash
open import BasicTypes
open import Prelude

import Abstract.Records

module Abstract.RecordChain {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash     : ByteString → Hash)
  -- And is colission resistant
  (hash-cr  : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    where

 open WithCryptoHash hash hash-cr
 open Abstract.Records ec hash hash-cr

 module WithPool
   -- The current record pool; abstracted by saying
   -- whether a record is in the pool or not.
   (IsInPool            : Record → Set)
   (IsInPool-irrelevant : ∀{r}(p₀ p₁ : IsInPool r) → p₀ ≡ p₁)
     where

  -- A record chain is a slice of the reflexive transitive closure with
  -- valid records only. Validity, in turn, is defined by recursion on the
  -- chain.

  -- One way of looking at a 'RecordChain r' is to think of it as 
  -- one path from the epoch's initial record to r.
  data RecordChain : Record → Set₁

  data Valid : ∀ {r} → RecordChain r → Record → Set₁

  data RecordChain where
    empty : ∀ {hᵢ} → RecordChain (I hᵢ)
    step  : ∀ {r r'}
          → (rc : RecordChain r) 
          → r ← r'
          → Valid rc r' 
          → {prf : IsInPool r'} 
          → RecordChain r'

  data Valid where
    ValidBlockInit : {b : Block} {hᵢ : Initial} 
                   → 1 ≤ bRound b → Valid (empty {hᵢ}) (B b)
    ValidBlockStep : {b : Block} {q : QC}
                   → (rc : RecordChain (Q q))
                   → qRound q < bRound b
                   → Valid rc (B b)
    ValidQC        : {q : QC} {b : Block}
                   → (rc : RecordChain (B b))
                   → qRound q ≡ bRound b
                   → Valid rc (Q q)

  ValidQ⇒Round≡ : ∀{b}{certB : RecordChain (B b)}{q : QC}
                → Valid certB (Q q)
                → qRound q ≡ bRound b   
  ValidQ⇒Round≡ (ValidQC certB x) = x

  prevBlock : ∀{q} → RecordChain (Q q) → Block
  prevBlock (step {r = B b} _ (B←Q _) _) = b

  -- Defition of 'previous_round' as in Paper Section 5.5
  currRound : ∀{r} → RecordChain r → Round
  currRound empty = 0
  currRound (step {r = r} _ _ _) = round r

  -- TODO: prev round should be defined for blocks only...
  prevRound : ∀{r} → RecordChain r → Round
  prevRound empty = 0
  prevRound (step rc (I←B x) vr) = 0
  prevRound (step rc (Q←B x) vr) = currRound rc
  prevRound (step rc (B←Q x) vr) = prevRound rc

  -- A k-chain (paper Section 5.2) is a sequence of
  -- blocks and quorum certificates for said blocks:
  --
  --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₖ ← Cₖ
  --
  -- Our datatype 𝕂-chain captures exactly that structure.
  --
  data 𝕂-chain : (k : ℕ){r : Record} → RecordChain r → Set₁ where
    0-chain : ∀{r}{rc : RecordChain r} → 𝕂-chain 0 rc
    s-chain : ∀{k r}{rc : RecordChain r}{b : Block}{q : QC}
            → (r←b : r   ← B b)
            → {prfB : IsInPool (B b)}
            → (vb  : Valid rc (B b))
            → (b←q : B b ← Q q)
            → {prfQ : IsInPool (Q q)}
            → (vq  : Valid (step rc r←b vb {prfB}) (Q q))
            → 𝕂-chain k rc
            → 𝕂-chain (suc k) (step (step rc r←b vb {prfB}) b←q vq {prfQ})

  -- Returns the round of the block heading the k-chain.
  kchainHeadRound : ∀{k r}{rc : RecordChain r} → 𝕂-chain k rc → Round
  kchainHeadRound (0-chain {r = r})          = round r
  kchainHeadRound (s-chain r←b vb b←q vq kk) = kchainHeadRound kk

  kchainBlock : ∀{k r}{rc : RecordChain r} → Fin k → 𝕂-chain k rc → Block
  kchainBlock zero    (s-chain {b = b} _ _ _ _ _) = b
  kchainBlock (suc x) (s-chain r←b vb b←q vq kk)  = kchainBlock x kk

  kchainBlockRound≤ : ∀{k r}{rc : RecordChain r}(x y : Fin k)(kc : 𝕂-chain k rc)
                    → x ≤Fin y → bRound (kchainBlock y kc) ≤ bRound (kchainBlock x kc)
  kchainBlockRound≤ = {!!}

  data 𝕂-chain-contigR : (k : ℕ){r : Record} → RecordChain r → Set₁ where
    0-chain : ∀{r}{rc : RecordChain r} → 𝕂-chain-contigR 0 rc
    s-chain : ∀{k r}{q' : QC}{rc : RecordChain r}{b : Block}
            → (r←b : r ← B b)
            → {prfB : IsInPool (B b)}
            → (vb  : Valid rc (B b))
            → bRound b ≡ suc (round r)
            → (b←q : B b ← Q q')
            → {prfQ : IsInPool (Q q')}
            → (vq  : Valid (step rc r←b vb {prfB}) (Q q'))
            → 𝕂-chain-contigR k rc
            → 𝕂-chain-contigR (suc k) (step (step rc r←b vb {prfB}) b←q vq {prfQ})

  𝕂-chain-contigR-𝓤 : ∀{r k}{rc : RecordChain r}
                         → (cRChain : 𝕂-chain-contigR k rc)
                         → 𝕂-chain k rc
  𝕂-chain-contigR-𝓤  0-chain = 0-chain
  𝕂-chain-contigR-𝓤  (s-chain q←b vb x b←q₊₁ vq cRChain) = s-chain q←b vb b←q₊₁ vq (𝕂-chain-contigR-𝓤 cRChain)

  _⟦_⟧ck : ∀{k r}{rc : RecordChain r} → 𝕂-chain-contigR k rc → Fin k → Block
  chain ⟦ ix ⟧ck = kchainBlock ix (𝕂-chain-contigR-𝓤 chain)

  -- States that a given record belongs in a record chain.
  data _∈RC_ (r₀ : Record) : ∀{r₁} → RecordChain r₁ → Set where
    here   : ∀{rc : RecordChain r₀} → r₀ ∈RC rc
    there  : ∀{r₁ r₂}{rc : RecordChain r₁}(p : r₁ ← r₂)(pv : Valid rc r₂)
           → r₀ ∈RC rc
           → {prf : IsInPool r₂}
           → r₀ ∈RC (step rc p pv {prf})

  -- This is the reflexive-transitive closure of _←_, as defined in 
  -- section 4.7 in the paper. Note it is different than the previous
  -- definition in the code. We must consider the 'reflexive' aspect as
  -- we can see in the paper's proof of S4.
  data _←⋆_ (r₁ : Record) : Record → Set₁ where
    ssRefl : r₁ ←⋆ r₁
    ssStep : ∀ {r r₂ : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂

  ------------------------
  -- Lemma 1

  InitialIrrel : (i j : Initial) → i ≡ j
  InitialIrrel mkInitial mkInitial = refl

  -- LemmaS1-1 states that a record that has been flagged as 'valid' (paper section 4.2)
  -- depends upon the initial record.
  lemmaS1-1 : {i : Initial}{r : Record}
            → RecordChain r
            → (I i) ←⋆ r
  lemmaS1-1 {i} {i₀} (empty {hᵢ}) rewrite InitialIrrel i hᵢ = ssRefl
  lemmaS1-1 {i} {r} (step rc r'←r vR)
    with vR
  ... | ValidBlockInit x = ssStep (lemmaS1-1 rc) r'←r
  ... | ValidBlockStep rc x = ssStep (lemmaS1-1 rc) r'←r
  ... | ValidQC rc x = ssStep (lemmaS1-1 rc) r'←r


  lemmaS1-2 : ∀{r₀ r₁ r₂}
            → r₀ ← r₂ → r₁ ← r₂
            → HashBroke ⊎ (r₀ ≡ r₁)
  lemmaS1-2 {i₀} {i₁} {b} (I←B i₀←b) (I←B i₁←b)
    with hash-cr (trans i₀←b (sym i₁←b))
  ... | inj₁ (i₀≢i₁ , hi₀≡hi₁) = inj₁ ( ( encodeR i₀ , encodeR i₁ ) , ( i₀≢i₁ , hi₀≡hi₁ ) )
  ... | inj₂ i₀≡i₁             = inj₂ (encodeR-inj i₀≡i₁)
  lemmaS1-2 {i} {q} {b} (I←B i←b) (Q←B q←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ i≡q               = contradiction (encodeR-inj i≡q) λ ()
  lemmaS1-2 {q} {i} {b} (Q←B q←b) (I←B i←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ i≡q               = contradiction (encodeR-inj i≡q) λ ()
  lemmaS1-2 {q₀} {q₁} {b} (Q←B q₀←b) (Q←B q₁←b)
     with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ (q₀≢q₁ , hq₀≡hq₁) = inj₁ ( ( encodeR q₀ , encodeR q₁ ) , ( q₀≢q₁ , hq₀≡hq₁ ) )
  ... | inj₂ q₁≡q₂             = inj₂ (encodeR-inj q₁≡q₂)
  lemmaS1-2 {b₀} {b₁} {q} (B←Q b₀←q) (B←Q b₁←q)
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

  Valid-round-≤ : ∀{r₀ r₁}
            → (rc : RecordChain r₀)
            → Valid rc r₁
            → round r₀ ≤ round r₁
  Valid-round-≤ empty (ValidBlockInit x) = z≤n
  Valid-round-≤ rc (ValidBlockStep rc x) = <⇒≤ x
  Valid-round-≤ rc (ValidQC rc refl)     = ≤-refl

  ←⋆-round-< : ∀{r₀ r₁}
             → RecordChain r₁
             → r₀ ←⋆ r₁
             → HashBroke ⊎ (round r₀ ≤ round r₁)
  ←⋆-round-< empty ssRefl                   = inj₂ z≤n
  ←⋆-round-< (step path x x₁) ssRefl        = inj₂ ≤-refl
  ←⋆-round-< (step path x vr₁) (ssStep r x₂)
    with lemmaS1-2 x₂ x
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl
    with ←⋆-round-< path r
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ rec = inj₂ (≤-trans rec (Valid-round-≤ path vr₁))

  lemmaS1-3 : ∀{r₀ r₁ r₂}
            → RecordChain r₀
            → RecordChain r₁
            → r₀ ←⋆ r₂ → r₁ ←⋆ r₂
            → round r₀ < round r₁
            → HashBroke ⊎ r₀ ←⋆ r₁
  lemmaS1-3 rc₀ rc₁ ssRefl ssRefl rr₀<rr₁ = inj₂ ssRefl
  lemmaS1-3 rc₀ rc₁ ssRefl (ssStep r₁←⋆r r←r₀) rr₀<rr₁
    with ←⋆-round-< rc₀ (ssStep r₁←⋆r r←r₀)
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ r₁≤r₀ = contradiction r₁≤r₀ (<⇒≱ rr₀<rr₁)
  lemmaS1-3 rc₀ rc₁ (ssStep r₀←⋆r r←r₁) ssRefl rr₀<rr₁ = inj₂ (ssStep r₀←⋆r r←r₁)
  lemmaS1-3 rc₀ rc₁ (ssStep r₀←⋆r r←r₂) (ssStep r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with ←-inj r←r₂ rₓ←r₂
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ refl = lemmaS1-3 rc₀ rc₁ r₀←⋆r r₁←⋆rₓ rr₀<rr₁

  ----------------------
  -- RecordChain Irrelevance
  --
  -- i.e., unless the hash was broken, there is always only
  --       one record chain up to a given record.
  
  ←-irrelevant : Irrelevant _←_
  ←-irrelevant (I←B x) (I←B y) = cong I←B (≡-irrelevant x y) 
  ←-irrelevant (Q←B x) (Q←B y) = cong Q←B (≡-irrelevant x y)
  ←-irrelevant (B←Q x) (B←Q y) = cong B←Q (≡-irrelevant x y)

  Valid-irrelevant : ∀{r r'}{rc : RecordChain r}(p₀ p₁ : Valid rc r') → p₀ ≡ p₁

  RecordChain-irrelevant : ∀{r}(rc₀ rc₁ : RecordChain r) → HashBroke ⊎ rc₀ ≡ rc₁
  RecordChain-irrelevant empty empty = inj₂ refl
  RecordChain-irrelevant (step rc0 rc0←r vr₀ {p0}) (step rc1 rc1←r vr₁ {p1}) 
    with lemmaS1-2 rc0←r rc1←r 
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl 
    with RecordChain-irrelevant rc0 rc1
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl rewrite ←-irrelevant rc1←r rc0←r 
     = inj₂ (cong₂ (λ P Q → step rc0 rc0←r P {Q}) 
                       (Valid-irrelevant vr₀ vr₁) 
                       (IsInPool-irrelevant p0 p1))

  Valid-irrelevant (ValidBlockInit x)    (ValidBlockInit x₁) 
    = cong ValidBlockInit (≤-irrelevant x x₁)
  Valid-irrelevant (ValidBlockStep rc x) (ValidBlockStep .rc x₁) 
    = cong (ValidBlockStep rc) (≤-irrelevant x x₁)
  Valid-irrelevant (ValidQC rc x)        (ValidQC .rc x₁) 
    = cong (ValidQC rc) (≡-irrelevant x x₁)

  -----------------
  -- Commit Rule --

  -- A block (and everything preceeding it) is said to match the commit rule
  -- when the block is the head of a contiguious 3-chain. Here we define an auxiliary
  -- datatype to make definitions more bearable.
  data CommitRule : ∀{r} → RecordChain r → Block → Set₁ where
    commit-rule : ∀{r b}{rc : RecordChain r}(c3 : 𝕂-chain-contigR 3 rc) 
                → b ≡ c3 ⟦ suc (suc zero) ⟧ck
                → CommitRule rc b
