open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types

module LibraBFT.Abstract.RecordChain.Properties
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec : EpochConfig)
   where

 open import LibraBFT.Abstract.BFT                         ec 
 open import LibraBFT.Abstract.Records                     ec 
 open        WithCryptoHash                                hash hash-cr
 open import LibraBFT.Abstract.Records.Extends             hash hash-cr ec
 open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
 open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec
 open import LibraBFT.Abstract.RecordStoreState.Invariants hash hash-cr ec
   as Invariants

 -- VCM: Only in this module we allow ourselves to compare VoteOrder's
 --      This ensures we can't inspect, nor use it anywhere else.
 private
   postulate <VO-cmp : Trichotomous _≡_ _<VO_

 module ForRSS -- VCM: I can't call this WithRSS because I 'open'ed stuff above
   {s}{RSS : Set s}⦃ isRSS : isRecordStoreState RSS ⦄
   (curr                  : RSS) 
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
           → IsInPool (Q q₀) → IsInPool (Q q₁)
             -- MSM rc₀ and rc₁ are not used.  Are they expected to be needed when we add state?
             -- Also, any reason not to separate rc₀ and p₀ with → ?
           → (rc₀ : RecordChain (B b₀))(p₀ : B b₀ ← Q q₀)
           → (rc₁ : RecordChain (B b₁))(p₁ : B b₁ ← Q q₁)
           → getRound b₀ ≡ getRound b₁
           → HashBroke ⊎ b₀ ≡ b₁ -- × qState q₀ ≡ qState q₁
   lemmaS2 {b₀} {b₁} {q₀} {q₁} p0 p1 rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
     with b₀ ≟Block b₁ -- (***)
   ...| yes done = inj₂ done
   ...| no  imp
     with lemmaB1 q₀ q₁
   ...|  (a , (a∈q₀ , a∈q₁ , honest))
     with <VO-cmp (voteOrder (∈QC-Vote q₀ a∈q₀)) (voteOrder (∈QC-Vote q₁ a∈q₁))
   ...| tri< va<va' _ _
     with increasing-round-rule a honest {q₀} {q₁} p0 p1 a∈q₀ a∈q₁ va<va'
   ...| res = ⊥-elim (<⇒≢ res hyp)
   lemmaS2 {b₀} {b₁} {q₀} {q₁} p0 p1 rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest))
      | tri> _ _ va'<va
     with increasing-round-rule a honest {q₁} {q₀} p1 p0 a∈q₁ a∈q₀ va'<va
   ...| res = ⊥-elim (<⇒≢ res (sym hyp))
   lemmaS2 {b₀} {b₁} {q₀} {q₁} p0 p1 rc₀ (B←Q refl h₀) rc₁ (B←Q refl h₁) hyp
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest))
      | tri≈ _ va≡va' _
     with votes-only-once-rule a honest {q₀} {q₁} p0 p1 a∈q₀ a∈q₁ va≡va'
   ...| v₀≡v₁ = let v₀∈q₀ = ∈QC-Vote-correct q₀ a∈q₀
                    v₁∈q₁ = ∈QC-Vote-correct q₁ a∈q₁
                in inj₁ ((encodeR (B b₀) , encodeR (B b₁)) , (imp ∘ B-inj ∘ encodeR-inj)
                        , trans h₀ (trans (vote≡⇒QPrevHash≡ {q₀} {q₁} v₀∈q₀ v₁∈q₁ v₀≡v₁) (sym h₁)))

   ----------------
   -- Lemma S3

   lemmaS3 : ∀{P r₂}{rc : RecordChain r₂}
           → (c3 : 𝕂-chain P 3 rc)        -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S3
           → {q' : QC}
           → (certB : RecordChain (Q q')) -- Immediatly before a (Q q), we have the certified block (B b), which is the 'B' in S3
           → round r₂ < getRound q'
           → getRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound certB
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} _ b₂←q₂ {pq} c2) {q'} (step certB b←q' {pq'}) hyp
     with lemmaB1 q₂ q'
   ...| (a , (a∈q₂ , a∈q' , honest))
     -- TODO: We have done a similar reasoning on the order of votes on lemmaS2; This is cumbersome
     -- and error prone. We should factor out a predicate that analyzes the rounds of QC's and
     -- returns us a judgement about the order of the votes.
     with <VO-cmp (voteOrder (∈QC-Vote q₂ a∈q₂)) (voteOrder (∈QC-Vote q' a∈q'))
   ...| tri> _ _ va'<va₂
     with increasing-round-rule a honest {q'} {q₂} pq' pq a∈q' a∈q₂ va'<va₂
   ...| res = ⊥-elim (n≮n (getRound q') (≤-trans res (≤-unstep hyp)))
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} P b₂←q₂ {pq} c2) {q'} (step certB b←q' {pq'}) hyp
      | (a , (a∈q₂ , a∈q' , honest))
      | tri≈ _ va₂≡va' _
     with votes-only-once-rule a honest {q₂} {q'} pq pq' a∈q₂ a∈q' va₂≡va'
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

   -- The base case for lemma S4 resorts to a pretty simple
   -- arithmetic statement.
   propS4-base-arith
     : ∀ n r
     → n ≤ r → r ≤ (suc (suc n))
     → r ∈ (suc (suc n) ∷ suc n ∷ n ∷ [])
   propS4-base-arith .0 .0 z≤n z≤n = there (there (here refl))
   propS4-base-arith .0 .1 z≤n (s≤s z≤n) = there (here refl)
   propS4-base-arith .0 .2 z≤n (s≤s (s≤s z≤n)) = here refl
   propS4-base-arith (suc r) (suc n) (s≤s h0) (s≤s h1) 
     = ∈-cong suc (propS4-base-arith r n h0 h1)

   -- Which is then translated to LibraBFT lingo
   propS4-base-lemma-1
     : ∀{q}{rc : RecordChain (Q q)}
     → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
     → (r : ℕ)
     → getRound (c3 b⟦ suc (suc zero) ⟧) ≤ r
     → r ≤ getRound (c3 b⟦ zero ⟧) 
     → r ∈ ( getRound (c3 b⟦ zero ⟧)
           ∷ getRound (c3 b⟦ (suc zero) ⟧)
           ∷ getRound (c3 b⟦ (suc (suc zero)) ⟧)
           ∷ [])
   propS4-base-lemma-1 (s-chain {b = b0} r←b0 p0 (B←Q refl b←q0) 
                       (s-chain {b = b1} r←b1 p1 (B←Q refl b←q1) 
                       (s-chain {r = R} {b = b2} r←b2 p2 (B←Q refl b←q2) 
                        0-chain))) r hyp0 hyp1 
     rewrite p0 | p1 | p2 = propS4-base-arith (suc (round R)) r hyp0 hyp1

   propS4-base-lemma-2
     : ∀{P k r}{rc : RecordChain r}
     → (c  : 𝕂-chain P k rc)
     → {b' : Block}(q' : QC) → IsInPool (Q q')
     → (certB : RecordChain (B b'))(ext : (B b') ← (Q q'))
     → (ix : Fin k)
     → getRound (kchainBlock ix c) ≡ getRound b'
     → HashBroke ⊎ (kchainBlock ix c ≡ b')
   propS4-base-lemma-2 (s-chain {rc = rc} r←b {prfB} prf b←q {prfQ} c) q' pq' certB ext zero hyp 
     = lemmaS2 prfQ pq' (step rc r←b {prfB}) b←q certB ext hyp 
   propS4-base-lemma-2 (s-chain r←b prf b←q c) 
                       q' pq' certB ext (suc ix) hyp 
     = propS4-base-lemma-2 c q' pq' certB ext ix hyp

   _<$>_ : ∀{a b}{A : Set a}{B : Set b} → (A → B) → HashBroke ⊎ A → HashBroke ⊎ B
   f <$> (inj₁ hb) = inj₁ hb
   f <$> (inj₂ x)  = inj₂ (f x)

   propS4-base : ∀{q}{rc : RecordChain (Q q)}
               → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
               → {q' : QC}
               → (certB : RecordChain (Q q'))
               → getRound (c3 b⟦ suc (suc zero) ⟧) ≤ getRound q'
               → getRound q' ≤ getRound (c3 b⟦ zero ⟧) 
               → HashBroke ⊎ B (c3 b⟦ suc (suc zero) ⟧) ∈RC certB
   propS4-base c3 {q'} (step {B b} certB (B←Q refl x₀) {pq₀}) hyp0 hyp1 
     with propS4-base-lemma-1 c3 (getRound b) hyp0 hyp1
   ...| here r 
     with propS4-base-lemma-2 c3 q' pq₀ certB (B←Q refl x₀) zero r
   ...| inj₁ hb  = inj₁ hb
   ...| inj₂ res 
     with 𝕂-chain-∈RC c3 zero (suc (suc zero)) z≤n res certB
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there (B←Q refl x₀) res')
   propS4-base c3 {q'} (step certB (B←Q refl x₀) {pq₀}) 
       hyp0 hyp1 
      | there (here r) 
     with propS4-base-lemma-2 c3 q' pq₀ certB (B←Q refl x₀) (suc zero) r 
   ...| inj₁ hb  = inj₁ hb 
   ...| inj₂ res 
     with 𝕂-chain-∈RC c3 (suc zero) (suc (suc zero)) (s≤s z≤n) res certB
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there (B←Q refl x₀) res')
   propS4-base c3 {q'} (step certB (B←Q refl x₀) {pq₀}) hyp0 hyp1 
      | there (there (here r)) 
     with propS4-base-lemma-2 c3 q' pq₀ certB (B←Q refl x₀) (suc (suc zero)) r
   ...| inj₁ hb  = inj₁ hb
   ...| inj₂ res 
     with 𝕂-chain-∈RC c3 (suc (suc zero)) (suc (suc zero)) (s≤s (s≤s z≤n)) res certB
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there (B←Q refl x₀) res')

   {-# TERMINATING #-}
   propS4 :  ∀{q}{rc : RecordChain (Q q)}
          → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
          → {q' : QC}
          → (certB : RecordChain (Q q'))
          → getRound (c3 b⟦ suc (suc zero) ⟧) ≤ getRound q'
          -- In the paper, the proposition states that B₀ ←⋆ B, yet, B is the block preceding
          -- C, which in our case is 'prevBlock certB'. Hence, to say that B₀ ←⋆ B is
          -- to say that B₀ is a block in the RecordChain that goes all the way to C.
          → HashBroke ⊎ B (c3 b⟦ suc (suc zero) ⟧) ∈RC certB
   propS4 {rc = rc} c3 {q} (step certB b←q {pq}) hyp
     with getRound q ≤?ℕ getRound (c3 b⟦ zero ⟧) 
   ...| yes rq≤rb₂ = propS4-base c3 {q} (step certB b←q {pq}) hyp rq≤rb₂
   propS4 {q} c3 {q'} (step certB b←q {pq}) hyp
      | no  rb₂<rq 
     with lemmaS3 c3 (step certB b←q {pq}) 
                     (subst (_< getRound q') 
                            (kchainBlockRoundZero-lemma c3) 
                            (≰⇒> rb₂<rq))
   ...| ls3 
     with certB | b←q
   ...| step certB' res | (B←Q rx x) 
     with certB' | res
   ...| empty | (I←B ry y) 
      = contradiction (n≤0⇒n≡0 ls3) 
                      (¬bRound≡0 (kchain-to-RecordChain-at-b⟦⟧ c3 (suc (suc zero))))
   ...| step {r = r} certB'' (B←Q refl res') {p''} | (Q←B {q = q*} ry y) 
     with propS4 c3 (step certB'' (B←Q refl res') {p''}) ls3 
   ...| inj₁ hb    = inj₁ hb
   ...| inj₂ final = inj₂ (there (B←Q rx x) (there (Q←B ry y) final))

   -------------------
   -- Theorem S5

   thmS5 : ∀{q q'}{rc : RecordChain (Q q)}{rc' : RecordChain (Q q')}
         → {b b' : Block}
         → CommitRule rc  b
         → CommitRule rc' b'
         → HashBroke ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc) -- Not conflicting means one extends the other.
   thmS5 {rc = rc} {rc'} (commit-rule c3 refl) (commit-rule c3' refl) 
     with <-cmp (getRound (c3 b⟦ suc (suc zero) ⟧)) (getRound (c3' b⟦ suc (suc zero) ⟧)) 
   ...| tri≈ _ r≡r' _ = inj₁ <$> (propS4 c3 rc' (≤-trans (≡⇒≤ r≡r') (kchain-round-≤-lemma' c3' (suc (suc zero))))) 
   ...| tri< r<r' _ _ = inj₁ <$> (propS4 c3 rc' (≤-trans (≤-unstep r<r') (kchain-round-≤-lemma' c3' (suc (suc zero))))) 
   ...| tri> _ _ r'<r = inj₂ <$> (propS4 c3' rc (≤-trans (≤-unstep r'<r) (kchain-round-≤-lemma' c3 (suc (suc zero))))) 
