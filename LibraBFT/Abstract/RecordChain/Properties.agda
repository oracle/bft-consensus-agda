{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

-- This module contains properties about RecordChains, culminating in
-- theorem S5, which is the main per-epoch correctness condition.  The
-- properties are based on the original version of the LibraBFT paper,
-- which was current when they were developed:
-- https://developers.diem.com/docs/assets/papers/diem-consensus-state-machine-replication-in-the-diem-blockchain/2019-06-28.pdf
-- Even though the implementation has changed since that version of the
-- paper, we do not need to redo these proofs because that affects only
-- the concrete implementation.  This demonstrates one advantage of
-- separating these proofs into abstract and concrete pieces.

module LibraBFT.Abstract.RecordChain.Properties
  (𝓔      : EpochConfig)(valid : ValidEpoch 𝓔)
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (𝓥      : VoteEvidence 𝓔 UID)
   where

 open import LibraBFT.Abstract.System                 𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.Records                𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.Records.Extends        𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.RecordChain            𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.BFT                    𝓔 valid UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.RecordChain.Invariants 𝓔 valid UID _≟UID_ 𝓥
   as Invariants

 open EpochConfig 𝓔
 open ValidEpoch valid

 module WithInvariants {ℓ}
   (InSys                 : Record → Set ℓ)
   (votes-only-once       : Invariants.VotesOnlyOnceRule InSys)
   (locked-round-rule     : Invariants.LockedRoundRule   InSys)
  where

   open All-InSys-props InSys

   ----------------------
   -- Lemma 2

   -- Lemma 2 states that there can be at most one certified block per
   -- round.  If two blocks have a quorum certificate for the same round,
   -- then they are equal or their unique identifier is not
   -- injective. This is required because, on the concrete side, this bId
   -- will be a hash function which might yield collisions.
   lemmaS2 : {b₀ b₁ : Block}{q₀ q₁ : QC}
           → InSys (Q q₀) → InSys (Q q₁)
           → (p₀ : B b₀ ← Q q₀)
           → (p₁ : B b₁ ← Q q₁)
           → getRound b₀ ≡ getRound b₁
           → NonInjective-≡ bId ⊎ b₀ ≡ b₁
   lemmaS2 {b₀} {b₁} {q₀} {q₁} ex₀ ex₁ (B←Q refl h₀) (B←Q refl h₁) refl
     with b₀ ≟Block b₁
   ...| yes done = inj₂ done
   ...| no  imp
     with lemmaB1 q₀ q₁
   ...|  (a , (a∈q₀ , a∈q₁ , honest))
      with All-lookup (qVotes-C4 q₀) (∈QC-Vote-correct q₀ a∈q₀) |
           All-lookup (qVotes-C4 q₁) (∈QC-Vote-correct q₁ a∈q₁)
   ...| a∈q₀rnd≡ | a∈q₁rnd≡
     with <-cmp (abs-vRound (∈QC-Vote q₀ a∈q₀)) (abs-vRound (∈QC-Vote q₁ a∈q₁))
   ...| tri< va<va' _ _ = ⊥-elim (<⇒≢ (subst₂ _<_ a∈q₀rnd≡ a∈q₁rnd≡ va<va') refl)
   lemmaS2 {b₀} {b₁} {q₀} {q₁} ex₀ ex₁ (B←Q refl h₀) (B←Q refl h₁) refl
      | no imp
      | (a , (a∈q₀ , a∈q₁ , honest))
      | a∈q₀rnd≡ | a∈q₁rnd≡
      | tri> _ _ va'<va = ⊥-elim (<⇒≢ (subst₂ _≤_ (cong suc a∈q₁rnd≡) a∈q₀rnd≡ va'<va) refl)
   lemmaS2 {b₀} {b₁} {q₀} {q₁} ex₀ ex₁ (B←Q refl h₀) (B←Q refl h₁) hyp
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest))
      | a∈q₀rnd≡ | a∈q₁rnd≡
      | tri≈ _ v₀≡v₁ _ =
     let v₀∈q₀ = ∈QC-Vote-correct q₀ a∈q₀
         v₁∈q₁ = ∈QC-Vote-correct q₁ a∈q₁
         ppp   = trans h₀ (trans (vote≡⇒QPrevId≡ {q₀} {q₁} v₀∈q₀ v₁∈q₁ (votes-only-once a honest ex₀ ex₁ a∈q₀ a∈q₁ v₀≡v₁))
                                 (sym h₁))
     in inj₁ ((b₀ , b₁) , (imp , ppp))

   ----------------
   -- Lemma S3

   lemmaS3 : ∀{r₂ q'}
             {rc : RecordChain r₂}      → InSys r₂
           → (rc' : RecordChain (Q q')) → InSys (Q q')  -- Immediately before a (Q q), we have the certified block (B b), which is the 'B' in S3
           → (c3 : 𝕂-chain Contig 3 rc)                 -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S3
           → round r₂ < getRound q'
           → NonInjective-≡ bId ⊎ (getRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound rc')
   lemmaS3 {r₂} {q'} ex₀ (step rc' b←q') ex₁ (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ _ b₂←q₂ c2) hyp
     with lemmaB1 q₂ q'
   ...| (a , (a∈q₂ , a∈q' , honest))
     -- TODO-1: We have done similar reasoning on the order of votes for
     -- lemmaS2. We should factor out a predicate that analyzes the rounds
     -- of QC's and returns us a judgement about the order of the votes.
     with All-lookup (qVotes-C4 q') (∈QC-Vote-correct q' a∈q') |
          All-lookup (qVotes-C4 q₂) (∈QC-Vote-correct q₂ a∈q₂)
   ...| a∈q'rnd≡ | a∈q₂rnd≡
     with <-cmp (round r₂) (abs-vRound (∈QC-Vote q' a∈q'))
   ...| tri> _ _ va'<va₂
     with subst₂ _<_ a∈q'rnd≡ a∈q₂rnd≡   (≤-trans va'<va₂ (≤-reflexive (sym a∈q₂rnd≡)))
   ...| res = ⊥-elim (n≮n (getRound q') (≤-trans res (≤-unstep hyp)))
   lemmaS3 {q' = q'} ex₀ (step rc' b←q') ex₁ (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ P b₂←q₂ c2) hyp
      | (a , (a∈q₂ , a∈q' , honest))
      | a∈q'rnd≡ | a∈q₂rnd≡
      | tri≈ _ v₂≡v' _ =
     let v₂∈q₂ = ∈QC-Vote-correct q₂ a∈q₂
         v'∈q' = ∈QC-Vote-correct q' a∈q'
      in ⊥-elim (<⇒≢ hyp (vote≡⇒QRound≡ {q₂} {q'} v₂∈q₂ v'∈q'
                                        (votes-only-once a honest {q₂} {q'} ex₀ ex₁ a∈q₂ a∈q'
                                                         (trans a∈q₂rnd≡ v₂≡v'))))
   lemmaS3 {r} {q'} ex₀ (step rc' b←q') ex₁  (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ P b₂←q₂ c2) hyp
      | (a , (a∈q₂ , a∈q' , honest))
      | a∈q'rnd≡ | a∈q₂rnd≡
      | tri< va₂<va' _ _
     with b←q'
   ...| B←Q rrr xxx
      = locked-round-rule a honest {q₂} {q'} ex₀ ex₁ (s-chain r←b₂ P b₂←q₂ c2) a∈q₂
                    (step rc' (B←Q rrr xxx)) a∈q'
                          (≤-trans (≤-reflexive (cong suc a∈q₂rnd≡))
                                   va₂<va')

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
   propS4-base-lemma-1 (s-chain {b = b0} _ p0 (B←Q refl b←q0)
                       (s-chain {b = b1} r←b1 p1 (B←Q refl b←q1)
                       (s-chain {r = R} {b = b2} r←b2 p2 (B←Q refl b←q2)
                          0-chain))) r hyp0 hyp1
     rewrite p0 | p1 = propS4-base-arith (bRound b2) r hyp0 hyp1

   propS4-base-lemma-2
     : ∀{k r}
       {rc : RecordChain r} → All-InSys rc
     → (q' : QC) → InSys (Q q')
     → {b' : Block}
     → (rc' : RecordChain (B b')) → (ext : (B b') ← (Q q'))
     → (c  : 𝕂-chain Contig k rc)
     → (ix : Fin k)
     → getRound (kchainBlock ix c) ≡ getRound b'
     → NonInjective-≡ bId ⊎ (kchainBlock ix c ≡ b')
   propS4-base-lemma-2 {rc = rc} prev∈sys q' q'∈sys rc' ext (s-chain r←b prf b←q c) zero hyp
     = lemmaS2 (All-InSys⇒last-InSys prev∈sys) q'∈sys b←q ext hyp
   propS4-base-lemma-2 prev∈sys q' q'∈sys rc' ext (s-chain r←b prf b←q c) (suc ix)
     = propS4-base-lemma-2 (All-InSys-unstep (All-InSys-unstep prev∈sys)) q' q'∈sys rc' ext c ix

   propS4-base : ∀{q q'}
               → {rc : RecordChain (Q q)}   → All-InSys rc
               → (rc' : RecordChain (Q q')) → InSys (Q q')
               → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
               → getRound (c3 b⟦ suc (suc zero) ⟧) ≤ getRound q'
               → getRound q' ≤ getRound (c3 b⟦ zero ⟧)
               → NonInjective-≡ bId ⊎ B (c3 b⟦ suc (suc zero) ⟧) ∈RC rc'
   propS4-base {q' = q'} prev∈sys (step {B b} rc'@(step rc'' q←b) b←q@(B←Q refl _)) q'∈sys c3 hyp0 hyp1
     with propS4-base-lemma-1 c3 (getRound b) hyp0 hyp1
   ...| here r
     with propS4-base-lemma-2 prev∈sys q' q'∈sys rc' b←q c3 zero (sym r)
   ...| inj₁ hb = inj₁ hb
   ...| inj₂ res
     with 𝕂-chain-∈RC c3 zero (suc (suc zero)) z≤n res rc'
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there b←q res')
   propS4-base {q} {q'} prev∈sys (step rc' (B←Q refl x₀)) q'∈sys c3 hyp0 hyp1
      | there (here r)
     with propS4-base-lemma-2 prev∈sys q' q'∈sys rc' (B←Q refl x₀) c3 (suc zero) (sym r)
   ...| inj₁ hb = inj₁ hb
   ...| inj₂ res
     with 𝕂-chain-∈RC c3 (suc zero) (suc (suc zero)) (s≤s z≤n) res rc'
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there (B←Q refl x₀) res')
   propS4-base {q' = q'} prev∈sys (step rc' (B←Q refl x₀)) q'∈sys c3 hyp0 hyp1
      | there (there (here r))
     with propS4-base-lemma-2 prev∈sys q' q'∈sys rc' (B←Q refl x₀) c3 (suc (suc zero)) (sym r)
   ...| inj₁ hb = inj₁ hb
   ...| inj₂ res
     with 𝕂-chain-∈RC c3 (suc (suc zero)) (suc (suc zero)) (s≤s (s≤s z≤n)) res rc'
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ res' = inj₂ (there (B←Q refl x₀) res')

   propS4 : ∀{q q'}
          → {rc : RecordChain (Q q)}   → All-InSys rc
          → (rc' : RecordChain (Q q')) → All-InSys rc'
          → (c3 : 𝕂-chain Contig 3 rc) -- This is B₀ ← C₀ ← B₁ ← C₁ ← B₂ ← C₂ in S4
          → getRound (c3 b⟦ suc (suc zero) ⟧) ≤ getRound q'
          -- In the paper, the proposition states that B₀ ←⋆ B, yet, B is the block preceding
          -- C, which in our case is 'prevBlock rc''. Hence, to say that B₀ ←⋆ B is
          -- to say that B₀ is a block in the RecordChain that goes all the way to C.
          → NonInjective-≡ bId ⊎ B (c3 b⟦ suc (suc zero) ⟧) ∈RC rc'
   propS4 {q' = q'} {rc} prev∈sys (step rc' b←q') prev∈sys' c3 hyp
     with getRound q' ≤?ℕ getRound (c3 b⟦ zero ⟧)
   ...| yes rq≤rb₂ = propS4-base {q' = q'} prev∈sys (step rc' b←q') (All-InSys⇒last-InSys prev∈sys') c3 hyp rq≤rb₂
   propS4 {q' = q'} prev∈sys (step rc' b←q') all∈sys c3 hyp
      | no  rb₂<rq
     with lemmaS3 (All-InSys⇒last-InSys prev∈sys) (step rc' b←q')
                  (All-InSys⇒last-InSys all∈sys) c3
                  (subst (_< getRound q') (kchainBlockRoundZero-lemma c3) (≰⇒> rb₂<rq))
   ...| inj₁ hb = inj₁ hb
   ...| inj₂ ls3
     with rc' | b←q'
   ...| step rc'' q←b | (B←Q {b} rx x)
     with rc'' | q←b
   ...| empty | (I←B _ _)
      = contradiction (n≤0⇒n≡0 ls3)
                      (¬bRound≡0 (kchain-to-RecordChain-at-b⟦⟧ c3 (suc (suc zero))))
   ...| step {r = r} rc''' (B←Q {q = q''} refl bid≡) | (Q←B ry y)
     with propS4 {q' = q''} prev∈sys (step rc''' (B←Q refl bid≡)) (All-InSys-unstep (All-InSys-unstep all∈sys)) c3 ls3
   ...| inj₁ hb'   = inj₁ hb'
   ...| inj₂ final = inj₂ (there (B←Q rx x) (there (Q←B ry y) final))

   -------------------
   -- Theorem S5
   thmS5 : ∀{q q'}
         → {rc  : RecordChain (Q q )} → All-InSys rc
         → {rc' : RecordChain (Q q')} → All-InSys rc'
         → {b b' : Block}
         → CommitRule rc  b
         → CommitRule rc' b'
         → NonInjective-≡ bId ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc) -- Not conflicting means one extends the other.
   thmS5 {rc = rc} prev∈sys {rc'} prev∈sys' (commit-rule c3 refl) (commit-rule c3' refl)
     with <-cmp (getRound (c3 b⟦ suc (suc zero) ⟧)) (getRound (c3' b⟦ suc (suc zero) ⟧))
   ...| tri≈ _ r≡r' _ = inj₁ <⊎$> (propS4 prev∈sys  rc' prev∈sys' c3  (≤-trans (≡⇒≤ r≡r')      (kchain-round-≤-lemma' c3' (suc (suc zero)))))
   ...| tri< r<r' _ _ = inj₁ <⊎$> (propS4 prev∈sys  rc' prev∈sys' c3  (≤-trans (≤-unstep r<r') (kchain-round-≤-lemma' c3' (suc (suc zero)))))
   ...| tri> _ _ r'<r = inj₂ <⊎$> (propS4 prev∈sys' rc  prev∈sys  c3' (≤-trans (≤-unstep r'<r) (kchain-round-≤-lemma' c3  (suc (suc zero)))))
