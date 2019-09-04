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

   open WithPool (_∈ pool curr)

   ----------------------
   -- Lemma 2

   module WithBFT 
      (lemmaB1 : (q₁ : QC)(q₂ : QC) 
               → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a))
     where


    -- TODO: When we bring in the state everywhere; this will remain very similar.
    --       We will add another check for st₀ ≟State st₁ after checking the block
    --       equality in (***); Naturally, if blocks are equal so is the state.
    --       We will need some command-application-injective lemma.
    --
    --         1) when st₀ ≟State st₁ returns yes, we done.
    --         2) when it returns no, and the blocks are different, no problem.
    --         3) when it returns no and the blocks are equal, its impossible! HashBroke!
    lemmaS2 : {q₀ q₁ : QC}
            → (rc₀ : RecordChain (Q q₀)) 
            → (rc₁ : RecordChain (Q q₁)) 
            → bRound (prevBlock rc₀) ≡ bRound (prevBlock rc₁)
            → HashBroke ⊎ prevBlock rc₀ ≡ prevBlock rc₁ -- × qState q₀ ≡ qState q₁
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
      with b₀ ≟Block b₁ -- (***)
    ...| yes done = inj₂ done
    ...| no  imp  
      with lemmaB1 q₀ q₁
    ...|  (a , (a∈q₀ , a∈q₁ , honest)) 
      with <-cmp (vOrder (∈QC-Vote {q₀} a a∈q₀)) (vOrder (∈QC-Vote {q₁} a a∈q₁))
    ...| tri< va<va' _ _ 
      with increasing-round-rule a honest {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀ 
                                          {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁ 
                                          va<va'
    ...| res = ⊥-elim (<⇒≢ res hyp)
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
       | no imp
       |  (a , (a∈q₀ , a∈q₁ , honest)) 
       | tri> _ _ va'<va 
      with increasing-round-rule a honest {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁  
                                          {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀  
                                          va'<va
    ...| res = ⊥-elim (<⇒≢ res (sym hyp))
    lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                      (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
       | no imp
       |  (a , (a∈q₀ , a∈q₁ , honest)) 
       | tri≈ _ va≡va' _ 
      with votes-only-once-rule a honest {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀  
                                         {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁ 
                                         va≡va'
    ...| res = inj₁ ((encodeR (B b₀) , encodeR (B b₁)) , (imp ∘ B-inj ∘ encodeR-inj) 
                     , trans h₀ {!!}) -- extract from h₁, res and qVotes-C3!


    -- We just noted that when the paper mentions 'certified' or ' verified'
    -- block, we encode it as a 'RecordChain' ending in said block.   
    lemmaS3 : ∀{r}{rc : RecordChain r}
            → (c3 : 𝕂-chain 3 rc)
            → {b' : Block}{q' : QC}
            → (certB : RecordChain (B b'))
            → (b←q   : B b' ← Q q') → Valid certB (Q q')
            → round r < bRound b'
            → bRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound certB 
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
      with lemmaB1 q₂ q'
    ...| (a , (a∈q₂ , a∈q' , honest)) 
      -- TODO: We have done a similar reasoning on the order of votes on lemmaS2; This is cumbersome
      -- and error prone. We should factor out a predicate that analyzes the rounds of QC's and
      -- returns us a judgement about the order of the votes.
      with <-cmp (vOrder (∈QC-Vote {q₂} a a∈q₂)) (vOrder (∈QC-Vote {q'} a a∈q'))
    ...| tri> _ _ va'<va₂ 
      with increasing-round-rule a honest (step certB b←q' vq')               a∈q' 
                                          (step (step rc r←b₂ vb₂) b₂←q₂ vq₂) a∈q₂ 
                                          va'<va₂ 
    ...| res rewrite ValidQ⇒Round≡ vq' = ⊥-elim (n≮n (bRound b') (≤-trans res (≤-unstep hyp)))
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
       | (a , (a∈q₂ , a∈q' , honest)) 
       | tri≈ _ va₂≡va' _ 
      with votes-only-once-rule a honest (step (step rc r←b₂ vb₂) b₂←q₂ vq₂) a∈q₂ 
                                         (step certB b←q' vq')               a∈q'
                                         va₂≡va'
    ...| res rewrite ValidQ⇒Round≡ vq' = {!!} -- res tells me both votes are the same; hyp tells
                                              -- me the rounds of the QC's are different; 
                                              -- votes can't be the same.
    lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
       | (a , (a∈q₂ , a∈q' , honest)) 
       | tri< va₂<va' _ _ 
      with b←q' 
    ...| B←Q xxx 
       with locked-round-rule a honest {q₂} (s-chain r←b₂ vb₂ b₂←q₂ vq₂ c2) a∈q₂ {q'} (step certB (B←Q xxx) vq') a∈q' va₂<va'
    ...| res = ≤-trans (kchainBlockRound≤ zero (suc zero) c2 z≤n) res

 {-
      with bRound b₂ ≤?ℕ bRound b'
    ...| no imp 
      with increasing-round-rule a honest (step _ b₂←q₂ vq₂) a∈q₂ 
    ...| abs = ⊥-elim (abs (irh (step certB b←q' vq') a∈q' {!!} {!!}))
    lemmaS3 {r} (s-chain {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
       | (a , (a∈q₂ , a∈q' , honest)) 
       | yes prf = {!!}
 -}
