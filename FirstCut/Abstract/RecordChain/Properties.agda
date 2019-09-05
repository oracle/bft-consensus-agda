open import Hash
open import BasicTypes
open import Lemmas
open import Prelude

open import Data.Nat.Properties

module Abstract.RecordChain.Properties {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 open WithCryptoHash                      hash hash-cr
 open import Abstract.Records          ec hash hash-cr
 open import Abstract.RecordChain      ec hash hash-cr
 open import Abstract.RecordStoreState ec hash hash-cr

 module ForRSS 
      (curr : RecordStoreState) 
      (increasing-round-rule : Invariants.IncreasingRoundRule curr)
      (votes-only-once-rule  : Invariants.VotesOnlyOnceRule   curr)
      (locked-round-rule     : Invariants.LockedRoundRule     curr)
     where

   open WithPool (_∈ pool curr) ∈-irrelevant

   module WithBFT 
      (lemmaB1 : (q₁ : QC)(q₂ : QC) 
               → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a))
     where

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

    vote≡⇒QH≡ : ∀ {q q'} {v v' : Vote} → v ∈ qVotes q → v' ∈ qVotes q' → v ≡ v' →  qBlockHash q ≡ qBlockHash q'
    vote≡⇒QH≡ {q} {q'} v∈q v'∈q' refl
      with witness v∈q (qVotes-C3 q) | witness v'∈q' (qVotes-C3 q')
    ... | refl | refl = refl

    lemmaS2 : {q₀ q₁ : QC}
            → (rc₀ : RecordChain (Q q₀)) 
            → (rc₁ : RecordChain (Q q₁)) 
            → bRound (prevBlock rc₀) ≡ bRound (prevBlock rc₁)
            → HashBroke ⊎ prevBlock rc₀ ≡ prevBlock rc₁ -- × qState q₀ ≡ qState q₁
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl) {pa}) 
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl) {pb}) hyp 
      with b₀ ≟Block b₁ -- (***)
    ...| yes done = inj₂ done
    ...| no  imp  
      with lemmaB1 q₀ q₁
    ...|  (a , (a∈q₀ , a∈q₁ , honest)) 
      with <-cmp (vOrder (∈QC-Vote q₀ a∈q₀)) (vOrder (∈QC-Vote q₁ a∈q₁))
    ...| tri< va<va' _ _ 
      with increasing-round-rule a honest {q₀} {q₁} a∈q₀ a∈q₁ va<va'
    ...| res = ⊥-elim (<⇒≢ res hyp)
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl) {pa})
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl) {pb}) hyp 
       | no imp
       |  (a , (a∈q₀ , a∈q₁ , honest)) 
       | tri> _ _ va'<va 
      with increasing-round-rule a honest {q₁} {q₀} a∈q₁ a∈q₀ va'<va
    ...| res = ⊥-elim (<⇒≢ res (sym hyp))
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl) {pa}) 
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl) {pb}) hyp 
       | no imp
       |  (a , (a∈q₀ , a∈q₁ , honest)) 
       | tri≈ _ va≡va' _ 
      with votes-only-once-rule a honest {q₀} {q₁} a∈q₀ a∈q₁ va≡va'
    ...| v₀≡v₁ = let v₀∈q₀ = ∈QC-Vote-correct q₀ a∈q₀
                     v₁∈q₁ = ∈QC-Vote-correct q₁ a∈q₁
                 in inj₁ ((encodeR (B b₀) , encodeR (B b₁)) , (imp ∘ B-inj ∘ encodeR-inj)
                         , trans h₀ (trans (vote≡⇒QH≡ {q₀} {q₁} v₀∈q₀ v₁∈q₁ v₀≡v₁) (sym h₁)))

    -- Just like lemma S2, but with the unrolled RecordChain; this is sometimes
    -- easier to call.
    lemmaS2' : {b₀ b₁ : Block}{q₀ q₁ : QC}
             → (rc₀ : RecordChain (B b₀))(p₀ : B b₀ ← Q q₀)(v₀ : Valid rc₀ (Q q₀))
             → (rc₁ : RecordChain (B b₁))(p₁ : B b₁ ← Q q₁)(v₁ : Valid rc₁ (Q q₁))
             → {prf0 : Q q₀ ∈ pool curr}
             → {prf1 : Q q₁ ∈ pool curr}
             → bRound b₀ ≡ bRound b₁
             → HashBroke ⊎ b₀ ≡ b₁ -- × qState q₀ ≡ qState q₁
    lemmaS2' rc0 (B←Q p0) v0 rc1 (B←Q p1) v1 {prf0} {prf1} hyp
      = lemmaS2 (step rc0 (B←Q p0) v0 {prf0}) (step rc1 (B←Q p1) v1 {prf1}) hyp


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
    lemmaS3 : ∀{r₂}{rc : RecordChain r₂}
            → (c3 : 𝕂-chain 3 rc)          -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S3
            → {q' : QC}
            → (certB : RecordChain (Q q')) -- Immediatly before a (Q q), we have the certified block (B b), which is the 'B' in S3
            → round r₂ < qRound q'
            → bRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound certB 
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} vb₂ b₂←q₂ {pq} vq₂ c2) {q'} (step certB b←q' vq' {pq'}) hyp 
      with lemmaB1 q₂ q'
    ...| (a , (a∈q₂ , a∈q' , honest)) 
      -- TODO: We have done a similar reasoning on the order of votes on lemmaS2; This is cumbersome
      -- and error prone. We should factor out a predicate that analyzes the rounds of QC's and
      -- returns us a judgement about the order of the votes.
      with <-cmp (vOrder (∈QC-Vote q₂ a∈q₂)) (vOrder (∈QC-Vote q' a∈q'))
    ...| tri> _ _ va'<va₂ 
      with increasing-round-rule a honest {q'} {q₂} a∈q' a∈q₂ va'<va₂ 
    ...| res = ⊥-elim (n≮n (qRound q') (≤-trans res (≤-unstep hyp)))
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} vb₂ b₂←q₂ {pq} vq₂ c2) {q'} (step certB b←q' vq' {pq'}) hyp 
       | (a , (a∈q₂ , a∈q' , honest)) 
       | tri≈ _ va₂≡va' _ 
      with votes-only-once-rule a honest {q₂} {q'} a∈q₂ a∈q' va₂≡va'
    ...| res = {!!} -- res tells me both votes are the same; hyp tells
                    -- me the rounds of the QC's are different; 
                    -- votes can't be the same.
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ {pb} vb₂ b₂←q₂ {pq} vq₂ c2) {q'} (step certB b←q' vq' {pq'}) hyp 
       | (a , (a∈q₂ , a∈q' , honest)) 
       | tri< va₂<va' _ _ 
      with b←q' 
    ...| B←Q xxx 
       with locked-round-rule a honest {q₂} (s-chain r←b₂ {pb} vb₂ b₂←q₂ {pq} vq₂ c2) a∈q₂ {q'} (step certB (B←Q xxx) vq' {{!!}}) a∈q' va₂<va'
    ...| res = ≤-trans (kchainBlockRound≤ zero (suc zero) c2 z≤n) res

   ------------------
   -- Proposition S4

    y+1+2-lemma : ∀{x y} → x ≤ y → y ≤ 2 + x
                → y ≡ x ⊎ y ≡ suc x ⊎ y ≡ suc (suc x)
    y+1+2-lemma hyp0 hyp1 = {!!}

    3chain-round-lemma
      : ∀{r}{rc : RecordChain r}(c3 : 𝕂-chain-contigR 3 rc)
      → bRound (c3 ⟦ zero ⟧ck) ≡ 2 + bRound (c3 ⟦ suc (suc zero) ⟧ck)
    3chain-round-lemma c3 = {!!}

    kchain-round-head-lemma
      : ∀{k r}{rc : RecordChain r}(c3 : 𝕂-chain-contigR (suc k) rc)
      → round r ≡ bRound (c3 ⟦ zero ⟧ck)
    kchain-round-head-lemma = {!!}

    kchain-round-≤-lemma
      : ∀{k r}{rc : RecordChain r}(c3 : 𝕂-chain-contigR k rc)(ix : Fin k)
      → bRound (c3 ⟦ ix ⟧ck) ≤ round r
    kchain-round-≤-lemma = {!!}

    kchain-to-RecordChain-Q
      : ∀{k r}{rc : RecordChain r}(c : 𝕂-chain-contigR k rc)(ix : Fin k)
      → RecordChain (Q (c ⟦ ix ⟧ck'))
    kchain-to-RecordChain-Q 0-chain () 
    kchain-to-RecordChain-Q (s-chain {rc = rc} r←b {pb} vb x b←q {pq} vq c) zero 
      = step (step rc r←b vb {pb}) b←q vq {pq}
    kchain-to-RecordChain-Q (s-chain r←b vb x b←q vq c) (suc zz) 
      = kchain-to-RecordChain-Q c zz
    
    kchain-to-RecordChain-Q-prevBlock
      : ∀{k r}{rc : RecordChain r}(c : 𝕂-chain-contigR k rc)(ix : Fin k)
      → prevBlock (kchain-to-RecordChain-Q c ix) ≡ c ⟦ ix ⟧ck
    kchain-to-RecordChain-Q-prevBlock (s-chain r←b vb x (B←Q b←q) vq c) zero = refl
    kchain-to-RecordChain-Q-prevBlock (s-chain r←b vb x (B←Q b←q) vq c) (suc ix) 
      = kchain-to-RecordChain-Q-prevBlock c ix
  
    propS4-base :  ∀{q}{rc : RecordChain (Q q)}
                → (c3 : 𝕂-chain-contigR 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
                → {q' : QC}
                → (certB : RecordChain (Q q'))
                → bRound (c3 ⟦ suc (suc zero) ⟧ck) ≤ qRound q'
                → qRound q' ≤ bRound (c3 ⟦ zero ⟧ck) 
                → HashBroke ⊎ B (c3 ⟦ suc (suc zero) ⟧ck) ∈RC certB
    propS4-base c3 (step (step empty (I←B x₁) vq₁ {pq₁}) (B←Q x₀) (ValidQC _ refl) {pq₀}) hyp0 hyp1 
      = {!!}
    propS4-base c3 (step (step certB (Q←B x₁) vq₁ {pq₁}) (B←Q x₀) vq₀ {pq₀}) hyp0 hyp1 = {!!}

    {-# TERMINATING #-}
    propS4 :  ∀{q}{rc : RecordChain (Q q)}
           → (c3 : 𝕂-chain-contigR 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
           → {q' : QC}
           → (certB : RecordChain (Q q'))
           → bRound (c3 ⟦ suc (suc zero) ⟧ck) ≤ qRound q'
           -- In the paper, the proposition states that B₀ ←⋆ B, yet, B is the block preceding
           -- C, which in our case is 'prevBlock certB'. Hence, to say that B₀ ←⋆ B is
           -- to say that B₀ is a block in the RecordChain that goes all the way to C.
           → HashBroke ⊎ B (c3 ⟦ suc (suc zero) ⟧ck) ∈RC certB
    propS4 {rc = rc} c3 {q} (step certB b←q vq {pq}) hyp
      with qRound q ≤?ℕ bRound (c3 ⟦ zero ⟧ck) 
    ...| yes rq≤rb₂ = propS4-base c3 (step certB b←q vq {pq}) hyp rq≤rb₂
{-
      with y+1+2-lemma hyp (subst (qRound q ≤_) (3chain-round-lemma c3) rq≤rb₂)
    ...| inj₁ case1 
      with lemmaS2 (kchain-to-RecordChain-Q c3 (suc (suc zero))) (step certB (B←Q b←q) (ValidQC _ refl) {pq}) 
                   (sym (trans case1 (cong bRound (sym (kchain-to-RecordChain-Q-prevBlock c3 (suc (suc zero)))))))  
    ...| inj₁ hb  = inj₁ hb
    ...| inj₂ res rewrite kchain-to-RecordChain-Q-prevBlock c3 (suc (suc zero)) | res 
       = inj₂ (there (B←Q b←q) (ValidQC _ refl) here)
    propS4 c3 {q} (step certB b←q vq {pq}) hyp
       | yes rq≤rb₂ 
       | inj₂ (inj₁ case2)  
      with lemmaS2 (kchain-to-RecordChain-Q c3 (suc zero)) {!!} 
                   (sym (trans case2 {!!}))  
    ...| inj₁ hb  = inj₁ hb
    ...| inj₂ res rewrite kchain-to-RecordChain-Q-prevBlock c3 (suc zero) | res 
       = inj₂ {!!}
    propS4 c3 {q} (step certB b←q vq {pq}) hyp
       | yes rq≤rb₂ 
       | inj₂ (inj₂ b≡b₀) = {!lemmaS2!}
-}
    propS4 c3 {q} (step certB b←q vq {pq}) hyp
       | no  rb₂<rq 
      with lemmaS3 (𝕂-chain-contigR-𝓤 c3) (step certB b←q vq {pq}) 
          ( subst (_< qRound q) (sym (kchain-round-head-lemma c3)) (≰⇒> rb₂<rq) )
    ...| ls3 
      with certB | b←q
    -- ...| empty | ()
    ...| step certB' res vres | (B←Q x) 
      with certB' | res
    ...| empty | (I←B y) = {!!} -- can't happen; no block has round 0, only Initial. Initial is not ot typ Block
    ...| step {r = r} certB'' res' (ValidQC xx refl) {p''} | (Q←B {q = q*} y) 
      with propS4 c3 (step certB'' res' (ValidQC xx refl) {p''}) ls3 
    ...| inj₁ hb    = inj₁ hb
    ...| inj₂ final = inj₂ (there (B←Q x) vq (there (Q←B y) vres final))
{-
      with propS4 c3 {!certB'!} {!!}
    ...| RES = there (B←Q x) vq (there res vres {!propS4!})
-}

    -------------------
    -- Theorem S5

    kchain-round-≤-lemma'
      : ∀{k q}{rc : RecordChain (Q q)}(c3 : 𝕂-chain-contigR k rc)(ix : Fin k)
      → bRound (c3 ⟦ ix ⟧ck) ≤ qRound q
    kchain-round-≤-lemma' = {!!}

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
    ...| tri≈ _ r≡r' _  = inj₁ <$> (propS4 c3 rc' (≤-trans (≡⇒≤ r≡r') {!!})) 
    ...| tri< r<r' _ _  = inj₁ <$> (propS4 c3 rc' {!!}) 
    ...| tri> _ _ r'<r' = inj₂ <$> (propS4 c3' rc {!!}) 
{-
    Translate the code below to with clauses returning HashBroke when needed

    ...| tri≈ _ r≡r' _  = inj₁ (propS4 c3 rc' {!!}) 
    ...| tri< r<r' _ _  = inj₁ (propS4 c3 rc' {!!}) 
    ...| tri> _ _ r'<r' = inj₂ (propS4 c3' rc {!!}) 
-}

