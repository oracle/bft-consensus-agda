open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

open import LibraBFT.Abstract.EpochConfig

module LibraBFT.Abstract.RecordChain.Properties {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 open import LibraBFT.Abstract.BFT                         ec 
 open import LibraBFT.Abstract.Records                     ec 
 open        WithCryptoHash                                   hash hash-cr
 open import LibraBFT.Abstract.Records.Extends             ec hash hash-cr
 open import LibraBFT.Abstract.RecordChain                 ec hash hash-cr
 open import LibraBFT.Abstract.RecordStoreState            ec hash hash-cr
 open import LibraBFT.Abstract.RecordStoreState.Invariants ec hash hash-cr
   as Invariants

 module ForRSS 
   {s}{RSS : Set s} (curr : isRecordStoreState RSS) 
   (correct               : Invariants.Correct             curr)
   (increasing-round-rule : Invariants.IncreasingRoundRule curr)
   (votes-only-once-rule  : Invariants.VotesOnlyOnceRule   curr)
   (locked-round-rule     : Invariants.LockedRoundRule     curr)
  where

   open WithRSS curr

   ----------------------
   -- Lemma 2


   -- TODO: When we bring in the state everywhere; this will remain very similar.
   --       We will add another check for st₀ ≟State st₁ after checking the block
   --       equality in (***); Naturally, if blocks are equal so is the state.
   --       We will need some command-application-injective lemma.
   --
   --         1) when st₀ ≟State st₁ returns yes, we done.
   --         2) when it returns no, and the blocks are different, no problem.
   --         3) when it returns no and the blocks are equal, its impossible! HashBroke!

   lemmaS2 : {b₀ b₁ : Block}{q₀ q₁ : QC}
           → (rc₀ : RecordChain (B b₀))(p₀ : B b₀ ← Q q₀)
           → (rc₁ : RecordChain (B b₁))(p₁ : B b₁ ← Q q₁)
           → bRound b₀ ≡ bRound b₁
           → HashBroke ⊎ b₀ ≡ b₁ -- × qState q₀ ≡ qState q₁
   lemmaS2 {b₀} {b₁} {q₀} {q₁} rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
     with b₀ ≟Block b₁ -- (***)
   ...| yes done = inj₂ done
   ...| no  imp
     with lemmaB1 q₀ q₁
   ...|  (a , (a∈q₀ , a∈q₁ , honest))
     with <-cmp (vOrder (∈QC-Vote q₀ a∈q₀)) (vOrder (∈QC-Vote q₁ a∈q₁))
   ...| tri< va<va' _ _
     with increasing-round-rule a honest {q₀} {q₁} a∈q₀ a∈q₁ va<va'
   ...| res = ⊥-elim (<⇒≢ res hyp)
   lemmaS2 {b₀} {b₁} {q₀} {q₁} rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest))
      | tri> _ _ va'<va
     with increasing-round-rule a honest {q₁} {q₀} a∈q₁ a∈q₀ va'<va
   ...| res = ⊥-elim (<⇒≢ res (sym hyp))
   lemmaS2 {b₀} {b₁} {q₀} {q₁} rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest))
      | tri≈ _ va≡va' _
     with votes-only-once-rule a honest {q₀} {q₁} a∈q₀ a∈q₁ va≡va'
   ...| v₀≡v₁ = let v₀∈q₀ = ∈QC-Vote-correct q₀ a∈q₀
                    v₁∈q₁ = ∈QC-Vote-correct q₁ a∈q₁
                in inj₁ ((encodeR (B b₀) , encodeR (B b₁)) , (imp ∘ B-inj ∘ encodeR-inj)
                        , trans h₀ (trans (vote≡⇒QPrevHash≡ {q₀} {q₁} v₀∈q₀ v₁∈q₁ v₀≡v₁) (sym h₁)))

   lemmaS2' : {q₀ q₁ : QC}
            → (rc₀ : RecordChain (Q q₀))
            → (rc₁ : RecordChain (Q q₁))
            → bRound (prevBlock rc₀) ≡ bRound (prevBlock rc₁)
            → HashBroke ⊎ prevBlock rc₀ ≡ prevBlock rc₁ -- × qState q₀ ≡ qState q₁
   lemmaS2' = {!!}

   ----------------
   -- Lemma S3

   -- MSM: Not sure I'm following this comment, but I think "certified" means there is a quorum
   -- certificate that references the block, while "verified" just means it was valid to add (so a
   -- block can be verified but not certified; however, it cannot be certified but not verified)..

   -- LPS && VCM: The first occurence of the string "certified" in the paper is at 4.2, the paper
   --  never defines what it actually means. Nevertheless, we have just found some simplification
   --  oppostunities while looking over our code trying to figure this out. We might be able to
   --  make the distinction you mention. We think it makes sense.

   -- VCM: Now that I come to think of it, the paper author's must use "certified" and "verified"
   --      interchangeably in this theorem.
   --      If a quorum of verifiers voted for block B at round C, it means they validated said block

   -- We just noted that when the paper mentions 'certified' or ' verified'
   -- block, we encode it as a 'RecordChain' ending in said block.
   lemmaS3 : ∀{P r₂}{rc : RecordChain r₂}
           → (c3 : 𝕂-chain P 3 rc)          -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S3
           → {q' : QC}
           → (certB : RecordChain (Q q')) -- Immediatly before a (Q q), we have the certified block (B b), which is the 'B' in S3
           → round r₂ < qRound (qBase q')
           → bRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound certB
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} _ b₂←q₂ {pq} c2) {q'} (step certB b←q' {pq'}) hyp
     with lemmaB1 q₂ q'
   ...| (a , (a∈q₂ , a∈q' , honest))
     -- TODO: We have done a similar reasoning on the order of votes on lemmaS2; This is cumbersome
     -- and error prone. We should factor out a predicate that analyzes the rounds of QC's and
     -- returns us a judgement about the order of the votes.
     with <-cmp (vOrder (∈QC-Vote q₂ a∈q₂)) (vOrder (∈QC-Vote q' a∈q'))
   ...| tri> _ _ va'<va₂
     with increasing-round-rule a honest {q'} {q₂} a∈q' a∈q₂ va'<va₂
   ...| res = ⊥-elim (n≮n (qRound (qBase q')) (≤-trans res (≤-unstep hyp)))
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} P b₂←q₂ {pq} c2) {q'} (step certB b←q' {pq'}) hyp
      | (a , (a∈q₂ , a∈q' , honest))
      | tri≈ _ va₂≡va' _
     with votes-only-once-rule a honest {q₂} {q'} a∈q₂ a∈q' va₂≡va'
   ...| v₂≡v' = let v₂∈q₂ = ∈QC-Vote-correct q₂ a∈q₂
                    v'∈q' = ∈QC-Vote-correct q' a∈q'
                in ⊥-elim (<⇒≢ hyp (vote≡⇒QRound≡ {q₂} {q'} v₂∈q₂ v'∈q' v₂≡v'))
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} P b₂←q₂ {pq} c2) {q'} (step certB b←q' {pq'}) hyp
      | (a , (a∈q₂ , a∈q' , honest))
      | tri< va₂<va' _ _
     with b←q'
   ...| B←Q rrr xxx
      with locked-round-rule a honest {q₂} (s-chain r←b₂ {pb} P b₂←q₂ {pq} c2) a∈q₂ {q'} (step certB (B←Q rrr xxx) {pq'}) a∈q' va₂<va'
   ...| res = ≤-trans (kchainBlockRound≤ zero (suc zero) c2 z≤n) res

  ------------------
  -- Proposition S4

   y+1+2-lemma : ∀{x y} → x ≤ y → y ≤ 2 + x
               → y ≡ x ⊎ y ≡ suc x ⊎ y ≡ suc (suc x)
   y+1+2-lemma hyp0 hyp1 = {!!}

   3chain-round-lemma
     : ∀{r}{rc : RecordChain r}(c3 : 𝕂-chain Contig 3 rc)
     → bRound (c3 ⟦ zero ⟧ck) ≡ 2 + bRound (c3 ⟦ suc (suc zero) ⟧ck)
   3chain-round-lemma c3 = {!!}

   kchain-round-head-lemma
     : ∀{k r}{rc : RecordChain r}(c3 : 𝕂-chain Contig (suc k) rc)
     → round r ≡ bRound (c3 ⟦ zero ⟧ck)
   kchain-round-head-lemma = {!!}

   kchain-round-≤-lemma
     : ∀{k r}{rc : RecordChain r}(c3 : 𝕂-chain Contig k rc)(ix : Fin k)
     → bRound (c3 ⟦ ix ⟧ck) ≤ round r
   kchain-round-≤-lemma = {!!}

   kchain-to-RecordChain-Q
     : ∀{k r}{rc : RecordChain r}(c : 𝕂-chain Contig k rc)(ix : Fin k)
     → RecordChain (Q (c ⟦ ix ⟧ck'))
   kchain-to-RecordChain-Q 0-chain () 
   kchain-to-RecordChain-Q (s-chain {rc = rc} r←b {pb} x b←q {pq} c) zero 
     = step (step rc r←b {pb}) b←q {pq}
   kchain-to-RecordChain-Q (s-chain r←b x b←q c) (suc zz) 
     = kchain-to-RecordChain-Q c zz

   kchain-to-RecordChain-B
     : ∀{k r}{rc : RecordChain r}(c : 𝕂-chain Contig k rc)(ix : Fin k)
     → RecordChain (B (c ⟦ ix ⟧ck))
   kchain-to-RecordChain-B 0-chain ()
   kchain-to-RecordChain-B (s-chain {rc = rc} r←b {pb} x b←q {pq} c) zero
     = (step rc r←b {pb})
   kchain-to-RecordChain-B (s-chain r←b x b←q c) (suc zz)
     = kchain-to-RecordChain-B c zz

   kchain-to-RecordChain-Q-prevBlock
     : ∀{k r}{rc : RecordChain r}(c : 𝕂-chain Contig k rc)(ix : Fin k)
     → prevBlock (kchain-to-RecordChain-Q c ix) ≡ c ⟦ ix ⟧ck
   kchain-to-RecordChain-Q-prevBlock (s-chain r←b x (B←Q r b←q) c) zero = refl
   kchain-to-RecordChain-Q-prevBlock (s-chain r←b x (B←Q r b←q) c) (suc ix) 
     = kchain-to-RecordChain-Q-prevBlock c ix

   propS4-base-lemma-1
     : ∀{q}{rc : RecordChain (Q q)}
     → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
     → {b' : Block}(q' : QC)
     → (certB : RecordChain (B b'))(ext : (B b') ← (Q q'))
     → bRound (c3 ⟦ suc (suc zero) ⟧ck) ≤ bRound b'
     → bRound b' ≤ bRound (c3 ⟦ zero ⟧ck) 
     → bRound b' ∈ ( bRound (c3 ⟦ zero ⟧ck)
                   ∷ bRound (c3 ⟦ (suc zero) ⟧ck)
                   ∷ bRound (c3 ⟦ (suc (suc zero)) ⟧ck)
                   ∷ [])
   propS4-base-lemma-1 = {!!}

   propS4-base-lemma-2
     : ∀{P k r}{rc : RecordChain r}
     → (c  : 𝕂-chain P k rc)
     → {b' : Block}(q' : QC)
     → (certB : RecordChain (B b'))(ext : (B b') ← (Q q'))
     → (ix : Fin k)
     → bRound (kchainBlock ix c) ≡ bRound b'
     → HashBroke ⊎ (kchainBlock ix c ≡ b')
   propS4-base-lemma-2 (s-chain {rc = rc} r←b {prfB} prf b←q {prfQ} c) q' certB ext zero hyp 
     = lemmaS2 (step rc r←b {prfB}) b←q certB ext hyp 
   propS4-base-lemma-2 (s-chain r←b prf b←q c) 
                       q' certB ext (suc ix) hyp 
     = propS4-base-lemma-2 c q' certB ext ix hyp

   propS4-base : ∀{q}{rc : RecordChain (Q q)}
               → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
               → {q' : QC}
               → (certB : RecordChain (Q q'))
               → bRound (c3 ⟦ suc (suc zero) ⟧ck) ≤ qRound (qBase q')
               → qRound (qBase q') ≤ bRound (c3 ⟦ zero ⟧ck) 
               → HashBroke ⊎ B (c3 ⟦ suc (suc zero) ⟧ck) ∈RC certB
   propS4-base c3 {q'} (step certB (B←Q refl x₀) {pq₀}) hyp0 hyp1 
     with propS4-base-lemma-1 c3 q' certB (B←Q refl x₀) hyp0 hyp1
   ...| here r 
     with propS4-base-lemma-2 c3 q' certB (B←Q refl x₀) zero r
   ...| inj₁ hb  = inj₁ hb
   ...| inj₂ res = inj₂ (there (B←Q refl x₀) 
                               (𝕂-chain-∈RC c3 zero (suc (suc zero)) z≤n res certB))
   propS4-base c3 {q'} (step certB (B←Q refl x₀) {pq₀}) 
       hyp0 hyp1 
      | there (here r) 
     with propS4-base-lemma-2 c3 q' certB (B←Q refl x₀) (suc zero) r 
   ...| inj₁ hb  = inj₁ hb 
   ...| inj₂ res = inj₂ (there (B←Q refl x₀) 
                               (𝕂-chain-∈RC c3 (suc zero) (suc (suc zero)) (s≤s z≤n) res certB))
   propS4-base c3 {q'} (step certB (B←Q refl x₀) {pq₀}) hyp0 hyp1 
      | there (there (here r)) 
     with propS4-base-lemma-2 c3 q' certB (B←Q refl x₀) (suc (suc zero)) r
   ...| inj₁ hb  = inj₁ hb
   ...| inj₂ res = inj₂ (there (B←Q refl x₀) 
                               (𝕂-chain-∈RC c3 (suc (suc zero)) (suc (suc zero)) (s≤s (s≤s z≤n)) res certB))

   {-# TERMINATING #-}
   propS4 :  ∀{q}{rc : RecordChain (Q q)}
          → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
          → {q' : QC}
          → (certB : RecordChain (Q q'))
          → bRound (c3 ⟦ suc (suc zero) ⟧ck) ≤ qRound (qBase q')
          -- In the paper, the proposition states that B₀ ←⋆ B, yet, B is the block preceding
          -- C, which in our case is 'prevBlock certB'. Hence, to say that B₀ ←⋆ B is
          -- to say that B₀ is a block in the RecordChain that goes all the way to C.
          → HashBroke ⊎ B (c3 ⟦ suc (suc zero) ⟧ck) ∈RC certB
   propS4 {rc = rc} c3 {q} (step certB b←q {pq}) hyp
     with qRound (qBase q) ≤?ℕ bRound (c3 ⟦ zero ⟧ck) 
   ...| yes rq≤rb₂ = propS4-base c3 {q} (step certB b←q {pq}) hyp rq≤rb₂
   propS4 c3 {q} (step certB b←q {pq}) hyp
      | no  rb₂<rq 
     with lemmaS3 c3 (step certB b←q {pq}) {!≰⇒> rb₂<rq -- then some magic with vq!}
   ...| ls3 
     with certB | b←q
   ...| step certB' res | (B←Q rx x) 
     with certB' | res
   ...| empty | (I←B ry y) 
      = contradiction (n≤0⇒n≡0 ls3) 
                      (¬bRound≡0 (kchain-to-RecordChain-B c3 (suc (suc zero))))
   ...| step {r = r} certB'' (B←Q refl res') {p''} | (Q←B {q = q*} ry y) 
     with propS4 c3 (step certB'' (B←Q refl res') {p''}) ls3 
   ...| inj₁ hb    = inj₁ hb
   ...| inj₂ final = inj₂ (there (B←Q rx x) (there (Q←B ry y) final))

   -------------------
   -- Theorem S5

   kchain-round-≤-lemma'
     : ∀{k q}{rc : RecordChain (Q q)}(c3 : 𝕂-chain Contig k rc)(ix : Fin k)
     → bRound (c3 ⟦ ix ⟧ck) ≤ qRound (qBase q)
   kchain-round-≤-lemma' (s-chain r←b x (B←Q refl b←q) c3) zero = ≤-refl
   kchain-round-≤-lemma' (s-chain (I←B prf imp) refl (B←Q refl _) 0-chain) (suc ()) 
   kchain-round-≤-lemma' (s-chain (Q←B prf imp) x (B←Q refl _) c2) (suc ix) 
     = ≤-trans (kchain-round-≤-lemma' c2 ix) (≤-unstep prf)

   _<$>_ : ∀{a b}{A : Set a}{B : Set b} → (A → B) → HashBroke ⊎ A → HashBroke ⊎ B
   f <$> (inj₁ hb) = inj₁ hb
   f <$> (inj₂ x)  = inj₂ (f x)

   thmS5 : ∀{q q'}{rc : RecordChain (Q q)}{rc' : RecordChain (Q q')}
         → {b b' : Block}
         → CommitRule rc  b
         → CommitRule rc' b'
         → HashBroke ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc) -- Not conflicting means one extends the other.
   thmS5 {rc = rc} {rc'} (commit-rule c3 refl) (commit-rule c3' refl) 
     with <-cmp (bRound (c3 ⟦ suc (suc zero) ⟧ck)) (bRound (c3' ⟦ suc (suc zero) ⟧ck)) 
   ...| tri≈ _ r≡r' _ = inj₁ <$> (propS4 c3 rc' (≤-trans (≡⇒≤ r≡r') (kchain-round-≤-lemma' c3' (suc (suc zero))))) 
   ...| tri< r<r' _ _ = inj₁ <$> (propS4 c3 rc' (≤-trans (≤-unstep r<r') (kchain-round-≤-lemma' c3' (suc (suc zero))))) 
   ...| tri> _ _ r'<r = inj₂ <$> (propS4 c3' rc (≤-trans (≤-unstep r'<r) (kchain-round-≤-lemma' c3 (suc (suc zero))))) 
