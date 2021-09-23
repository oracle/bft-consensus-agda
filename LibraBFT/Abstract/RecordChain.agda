{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Abstract.Types.EpochConfig
open import LibraBFT.Base.Types
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open        WithAbsVote

-- This module defines RecordChains and related types and utility definitions

module LibraBFT.Abstract.RecordChain
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (NodeId : Set)
  (𝓔      : EpochConfig UID NodeId)
  (𝓥      : VoteEvidence UID NodeId 𝓔)
  where
 open import LibraBFT.Abstract.Records         UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.Records.Extends UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.Types           UID        NodeId
 open        EpochConfig 𝓔

 -- One way of looking at a 'RecordChain r' is as a path from the epoch's
 -- initial record (I) to r.  For generality, we express this in two steps.
 data RecordChainFrom (o : Record) : Record → Set where
   empty : RecordChainFrom o o
   step  : ∀ {r r'}
         → (rc : RecordChainFrom o r)
         → r ← r'
         → RecordChainFrom o r'

 RecordChain : Record → Set
 RecordChain = RecordChainFrom I

 prevBlock : ∀{q} → RecordChain (Q q) → Block
 prevBlock (step {r = B b} _ (B←Q _ _)) = b

 prevQCorI : ∀{b} → RecordChain (B b) → Record
 prevQCorI (step _ (I←B _ _))           = I
 prevQCorI (step {r = Q q} _ (Q←B _ _)) = Q q

 -- Returns the unique identifier of the parent tagged to be either
 -- the initial block or a B or Q.
 parentUID : ∀{b} → RecordChain (B b) → TypedUID
 parentUID (step {r = I} _ _)   = id-I
 parentUID (step {r = Q q} _ _) = id-B∨Q (qCertBlockId q)

 -- Defition of 'previous_round' as in Section 5.5 (see Abstract.Properties).
 currRound : ∀{r} → RecordChain r → Round
 currRound empty = 0
 currRound (step {r = r} _ _) = round r

 -- TODO-1: it would be cleaner to define prevRound only for RecordChains ending in a Block.
 prevRound : ∀{r} → RecordChain r → Round
 prevRound empty = 0
 prevRound (step rc (I←B x vr)) = 0
 prevRound (step rc (Q←B x vr)) = currRound rc
 prevRound (step rc (B←Q x vr)) = prevRound rc

 -- Extensional definition of prevRound; useful to 'rewrite' on.
 prevRound-ss : ∀{b₁ q b}(rc : RecordChain (B b₁))
              → (ext₁ : B b₁ ← Q q)
              → (ext₀ : Q q  ← B b)
              → prevRound (step (step rc ext₁) ext₀) ≡ bRound b₁
 prevRound-ss rc (B←Q _ _) (Q←B _ _) = refl

 ----------------------
 -- RecordChain Equality and Irrelevance
 --

 -- Distributing a record relation pointwise
 -- over record chains. Let rc₀ and rc₁ be as illustrated
 -- below; a value of type ≈RC-pw, named prf is shown
 -- in between them.
 --
 --  rc₀    : B₀ ← C₀  ← B₁ ← C₁ ← ⋯ ← Bₖ  ← Cₖ
 --
 --  prf      ≈    ≈     ≈    ≈        ≈     ≈
 --
 --  rc₁    : 𝓑₀ ← 𝓒₀ ← 𝓑₁ ← 𝓒₁ ← ⋯ ← 𝓑ₖ ← 𝓒ₖ
 --
 --
 data ≈RC-pw {ℓ}(_≈_ : Rel Record ℓ)
     : ∀{o₀ o₁ r₀ r₁} → RecordChainFrom o₀ r₀ → RecordChainFrom o₁ r₁ → Set ℓ where
   eq-empty : ∀{o₀ o₁} → o₀ ≈ o₁ → ≈RC-pw _≈_ (empty {o = o₀}) (empty {o = o₁})
   eq-step  : ∀{o₀ o₁ r₀ r₁ s₀ s₁}
            → (rc₀ : RecordChainFrom o₀ s₀)
            → (rc₁ : RecordChainFrom o₁ s₁)
            → r₀ ≈ r₁
            → (ext₀ : s₀ ← r₀)
            → (ext₁ : s₁ ← r₁)
            → ≈RC-pw _≈_ rc₀ rc₁
            → ≈RC-pw _≈_ (step rc₀ ext₀) (step rc₁ ext₁)

 -- RecordChain equivalence is then defined in terms of
 -- record equivalence (i.e., we don't care about the set of
 -- votes for the QCs in the chain); borrowing the illustration
 -- above, we now have:
 --
 --  rc₀    : B₀ ← C₀  ← B₁ ← C₁ ← ⋯ ← Bₖ  ← Cₖ
 --
 --  prf      ≡    ≈QC   ≡    ≈QC      ≡     ≈QC
 --
 --  rc₁    : 𝓑₀ ← 𝓒₀ ← 𝓑₁ ← 𝓒₁ ← ⋯ ← 𝓑ₖ ← 𝓒ₖ
 --
 -- It is easy to see that if rc₀ ≈RC rc₁, then they contain
 -- the same blocks (propositionally!) but potentially
 -- different /sets of votes/ certifying said blocks.
 _≈RC_ : ∀{o₀ o₁ r₀ r₁} → RecordChainFrom o₀ r₀ → RecordChainFrom o₁ r₁ → Set
 _≈RC_ = ≈RC-pw _≈Rec_

 ≈RC-sym : ∀{o₀ o₁ r₀ r₁}{rc₀ : RecordChainFrom o₀ r₀}{rc₁ : RecordChainFrom o₁ r₁}
         → rc₀ ≈RC rc₁ → rc₁ ≈RC rc₀
 ≈RC-sym (eq-empty x) = eq-empty (≈Rec-sym x)
 ≈RC-sym (eq-step rc₀ rc₁ x ext₀ ext₁ hyp) = eq-step rc₁ rc₀ (≈Rec-sym x) ext₁ ext₀ (≈RC-sym hyp)

 ≈RC-trans : ∀ {r₀ r₁ r₂}
           → {rc₀ : RecordChain r₀}{rc₁ : RecordChain r₁}{rc₂ : RecordChain r₂}
           → rc₀ ≈RC rc₁ → rc₁ ≈RC rc₂ → rc₀ ≈RC rc₂
 ≈RC-trans (eq-empty x) q = q
 ≈RC-trans (eq-step rc₀ rc₁ x ext₀ ext₁ p) (eq-step .rc₁ rc₂ x₁ .ext₁ ext₂ q)
    = eq-step rc₀ rc₂ (≈Rec-trans x x₁) ext₀ ext₂ (≈RC-trans p q)

 --------------------------
 -- RecordChain elements

 data _∈RC-simple_ {o : Record}(r₀ : Record) : ∀{r₁} → RecordChainFrom o r₁ → Set where
   here   : ∀{rc : RecordChainFrom o r₀} → r₀ ∈RC-simple rc
   there  : ∀{r₁ r₂}{rc : RecordChainFrom o r₁}(p : r₁ ← r₂)
          → r₀ ∈RC-simple rc
          → r₀ ∈RC-simple (step rc p)

 ∈RC-simple-¬here : ∀ {o r r₀ r₁}
                    → (rcf : RecordChainFrom o r₀)
                    → (ext : r₀ ← r₁)
                    → ¬( r ≡ r₁ )
                    → r ∈RC-simple (step rcf ext)
                    → r ∈RC-simple rcf
 ∈RC-simple-¬here _ _ r≢r₁ r∈rcf+
    with r∈rcf+
 ... | here = ⊥-elim (r≢r₁ refl)
 ... | there _ xxx = xxx

  -- States that a given record belongs in a record chain.
 data _∈RC_ {o : Record}(r₀ : Record) : ∀{r₁} → RecordChainFrom o r₁ → Set where
   here   : ∀{rc : RecordChainFrom o r₀} → r₀ ∈RC rc
   there  : ∀{r₁ r₂}{rc : RecordChainFrom o r₁}(p : r₁ ← r₂)
          → r₀ ∈RC rc
          → r₀ ∈RC (step rc p)
   -- This is an important rule. It is the equivalent of a
   -- /congruence/ on record chains and enables us to prove
   -- the 𝕂-chain-∈RC property.
   transp : ∀{r}{rc₀ : RecordChainFrom o r}{rc₁ : RecordChainFrom o r}
          → r₀ ∈RC rc₀ → rc₀ ≈RC rc₁ → r₀ ∈RC rc₁

 ∈RC-empty-I : ∀{r} → r ∈RC (empty {o = I}) → r ≡ I
 ∈RC-empty-I here                      = refl
 ∈RC-empty-I (transp old (eq-empty x)) = ∈RC-empty-I old

 b∉RCempty : ∀ {b} → B b ∈RC empty → ⊥
 b∉RCempty xx with ∈RC-empty-I xx
 ...| ()

 transp-B∈RC : ∀{r r' b}{rc : RecordChain r}{rc' : RecordChain r'}
             → rc ≈RC rc' → B b ∈RC rc → B b ∈RC rc'
 transp-B∈RC rc≈rc' (transp b∈rc x) = transp-B∈RC (≈RC-trans x rc≈rc') b∈rc
 transp-B∈RC (eq-step rc₀ rc₁ (eq-B refl) ext₀ ext₁ rc≈rc') here = here
 transp-B∈RC (eq-step rc₀ rc₁ x .p ext₁ rc≈rc') (there p b∈rc) = there ext₁ (transp-B∈RC rc≈rc' b∈rc)

 ≈RC-head : ∀{o₀ o₁ r₀ r₁}{rc₀ : RecordChainFrom o₀ r₀}{rc₁ : RecordChainFrom o₁ r₁}
          → rc₀ ≈RC rc₁ → o₀ ≈Rec o₁
 ≈RC-head (eq-empty x)          = x
 ≈RC-head (eq-step _ _ _ _ _ x) = ≈RC-head x

 -- Heterogeneous irrelevance of _≈RC_ happens only modulo
 -- propositional non-injectivity of block ids.
 ≈RC-refl : ∀{r₀ r₁}(rc₀ : RecordChain r₀)(rc₁ : RecordChain r₁)
          → r₀ ≈Rec r₁
          → NonInjective-≡-preds (_∈RC-simple rc₀ ∘ B) (_∈RC-simple rc₁ ∘ B) bId ⊎ (rc₀ ≈RC rc₁)
 ≈RC-refl empty empty hyp
    = inj₂ (eq-empty hyp)
 ≈RC-refl (step r0 x) (step r1 x₁) hyp
    with ←-≈Rec x x₁ hyp
 ...| inj₁ (hb , (refl ,  refl)) = inj₁ (hb , there x here , there x₁ here) 
 ...| inj₂ cont
    with ≈RC-refl r0 r1 cont
 ...| inj₁ (¬inj , (x1 , x2)) = inj₁ (¬inj , (there x x1 , there x₁ x2))
 ...| inj₂ xx = inj₂ $ eq-step r0 r1 hyp x x₁ xx
 ≈RC-refl empty (step r1 (I←B x x₁)) ()
 ≈RC-refl empty (step r1 (Q←B x x₁)) ()
 ≈RC-refl empty (step r1 (B←Q x x₁)) ()
 ≈RC-refl (step r0 (I←B x x₁)) empty ()
 ≈RC-refl (step r0 (Q←B x x₁)) empty ()
 ≈RC-refl (step r0 (B←Q x x₁)) empty ()

 -- Heterogeneous irrelevance proves that two record chains that end at the same record
 -- have the same blocks and equivalent QCs.
 RecordChain-irrelevant : ∀{r}(rc₀ : RecordChain r)(rc₁ : RecordChain r)
                        → NonInjective-≡-preds (_∈RC-simple rc₀ ∘ B) (_∈RC-simple rc₁ ∘ B) bId ⊎ rc₀ ≈RC rc₁
 RecordChain-irrelevant rc0 rc1 = ≈RC-refl rc0 rc1 ≈Rec-refl

 -------------------------------------------------
 -- Sub RecordChains

 -- A value of type '⊆RC-pw _≈_ rc1 rc2' establishes that rc1 is
 -- a suffix of rc2 modulo _≈_.
 data ⊆RC-pw {ℓ}(_≈_ : Rel Record ℓ)
     : ∀{o₀ o₁ r₀ r₁} → RecordChainFrom o₀ r₀ → RecordChainFrom o₁ r₁ → Set ℓ where
   sub-empty : ∀{o₀ o₁ s₁}{r₁ : RecordChainFrom o₁ s₁} → o₀ ≈ s₁ → ⊆RC-pw _≈_ (empty {o = o₀}) r₁
   sub-step  : ∀{o₀ o₁ r₀ r₁ s₀ s₁}
            → (rc₀ : RecordChainFrom o₀ s₀)
            → (rc₁ : RecordChainFrom o₁ s₁)
            → r₀ ≈ r₁
            → (ext₀ : s₀ ← r₀)
            → (ext₁ : s₁ ← r₁)
            → ⊆RC-pw _≈_ rc₀ rc₁
            → ⊆RC-pw _≈_ (step rc₀ ext₀) (step rc₁ ext₁)

 _⊆RC_ : ∀{o₀ o₁ r₀ r₁} → RecordChainFrom o₀ r₀ → RecordChainFrom o₁ r₁ → Set
 _⊆RC_ = ⊆RC-pw _≈Rec_

 -- The ⊆RC relation is used to establish irrelevance of suffixes
 RecordChainFrom-irrelevant : ∀{o₀ o₁ r₀ r₁}(rc₀ : RecordChainFrom o₀ r₀)(rc₁ : RecordChainFrom o₁ r₁)
                            → r₀ ≈Rec r₁
                            → NonInjective-≡-preds (_∈RC-simple rc₀ ∘ B) (_∈RC-simple rc₁ ∘ B) bId ⊎ (rc₀ ⊆RC rc₁ ⊎ rc₁ ⊆RC rc₀)
 RecordChainFrom-irrelevant empty empty hyp = inj₂ (inj₁ (sub-empty hyp))
 RecordChainFrom-irrelevant empty (step rc1 x) hyp = inj₂ (inj₁ (sub-empty hyp))
 RecordChainFrom-irrelevant (step rc0 x) empty hyp = inj₂ (inj₂ (sub-empty (≈Rec-sym hyp)))
 RecordChainFrom-irrelevant (step rc0 x) (step rc1 x₁) hyp
    with ←-≈Rec x x₁ hyp
 ...| inj₁ (hb , (refl , refl)) = inj₁ (hb , (there x here) , (there x₁ here))
 ...| inj₂ cont
    with RecordChainFrom-irrelevant rc0 rc1 cont
 ...| inj₁ (hb , (z1 , z2)) = inj₁ (hb , (there x z1) , (there x₁ z2))
 ...| inj₂ cont1 = inj₂ $ either (inj₁ ∘ sub-step rc0 rc1 hyp x x₁) (inj₂ ∘ sub-step rc1 rc0 (≈Rec-sym hyp) x₁ x) cont1

 -- If a chain from the initial record is a suffix from a second chain,
 -- then the second chain is also from the initial record.
 RecordChain-glb : ∀{o' r r'}{rc : RecordChain r}{rcf : RecordChainFrom o' r'}
                 → rc ⊆RC rcf
                 → rc ≈RC rcf
 RecordChain-glb {rcf = step _ ()} (sub-empty eq-I)
 RecordChain-glb {rcf = empty}     (sub-empty eq-I) = eq-empty eq-I
 RecordChain-glb (sub-step rc₀ rc₁ x ext₀ ext₁ sub) = eq-step rc₀ rc₁ x ext₀ ext₁ (RecordChain-glb sub)

 -------------------------------------------------
 -- Id congruences over RecordChain equivalences

 parentUID-≈ : ∀{b₀ b₁}(rc₀ : RecordChain (B b₀))(rc₁ : RecordChain (B b₁))
             → rc₀ ≈RC rc₁
             → parentUID rc₀ ≡ parentUID rc₁
 parentUID-≈ _ _ (eq-step _ _ (eq-B refl) _ _ (eq-empty x)) = refl
 parentUID-≈ _ _ (eq-step _ _ (eq-B refl) _ _ (eq-step _ _ (eq-Q refl) _ _ _)) = refl

 -- A k-chain (paper Section 5.2; see Abstract.Properties) is a sequence of
 -- blocks and quorum certificates for said blocks:
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₖ ← Cₖ
 --
 -- such that for each Bᵢ some predicate R is satisfies for Bᵢ and Bᵢ₊₁.
 -- The first parameter R enables predicate definitions to avoid the need
 -- to find a predecessor for B₀ (see Contig definition below).
 --
 -- The 𝕂-chain datatype captures exactly that structure.
 --
 data 𝕂-chain (R : ℕ → Record → Record → Set)
     : (k : ℕ){o r : Record} → RecordChainFrom o r → Set where
   0-chain : ∀{o r}{rc : RecordChainFrom o r} → 𝕂-chain R 0 rc
   s-chain : ∀{k o r}{rc : RecordChainFrom o r}{b : Block}{q : QC}
           → (r←b : r   ← B b)
           → (prf : R k r (B b))
           → (b←q : B b ← Q q)
           → 𝕂-chain R k rc
           → 𝕂-chain R (suc k) (step (step rc r←b) b←q)

 -- Simple 𝕂-chains do not impose any restricton on its records.
 Simple : ℕ → Record → Record → Set
 Simple _ _ _ = Unit

 -- Contiguous 𝕂-chains are those in which all adjacent pairs of Records have contiguous rounds.
 Contig : ℕ → Record → Record → Set
 Contig 0       _  _ = Unit
 Contig (suc _) r r' = round r' ≡ suc (round r)

 -- The 'Contig' relation is substitutive in a rather restrictive setting,
 -- but this is enough for our purposes.
 Contig-subst : ∀{k r r' b}{rc : RecordChain r}{rc' : RecordChain r'}
              → rc ≈RC rc'
              → r ← (B b)
              → Contig k r (B b) → Contig k r' (B b)
 Contig-subst {zero}  _            _ _  = unit
 Contig-subst {suc k} (eq-empty x) _ cr = cr
 Contig-subst {suc k} (eq-step .(step rc₀ ext₂) .(step rc₁ ext₃) (eq-Q x) (B←Q refl refl) (B←Q refl refl)
                    (eq-step rc₀ rc₁ (eq-B refl) ext₂ ext₃ rc≈rc')) (Q←B h0 h1) cr = cr

 -- Consequently, contiguous 𝕂-chains are substitutive w.r.t. _≈RC_
 transp-𝕂-chain : ∀{k r r'}{rc : RecordChain r}{rc' : RecordChain r'}
                → rc ≈RC rc'
                → 𝕂-chain Contig k rc
                → 𝕂-chain Contig k rc'
 transp-𝕂-chain rc≈rc' 0-chain = 0-chain
 transp-𝕂-chain (eq-step .(step rc₀ r←b) .(step rc₁ r←b') (eq-Q refl) _ ext₁
                   (eq-step rc₀ rc₁ (eq-B refl) .r←b r←b' rc≈rc'))
                (s-chain r←b prf (B←Q _ _) kc) =
    s-chain r←b' (Contig-subst rc≈rc' r←b prf) ext₁ (transp-𝕂-chain rc≈rc' kc)

 -- TODO-2: Consider duplicating the above for the ⊆RC relation.
 -- I believe we can generalize all of this via the same function, but
 -- it's nontrivial to change the whole module.
 --
 -- Arguably, the right way to deal with all of this would be to
 -- design the bare record chain type as the most expressive possible:
 --
 -- data RC : ℕ → Record → Record
 --
 -- Then, a value r of type 'RC 12 I (B b)' represents a record chain with
 -- 12 steps from I to (B b). K-chains become trivial to express:
 --
 -- K-chain k = RC (2*k) ...

 Contig-subst-⊆ : ∀{k o o' r r' b}{rc : RecordChainFrom o r}{rc' : RecordChainFrom o' r'}
                → (kc : 𝕂-chain Contig k rc)
                → rc ⊆RC rc'
                → r ← (B b)
                → Contig k r (B b) → Contig k r' (B b)
 Contig-subst-⊆ 0-chain _ ext hyp = unit
 Contig-subst-⊆ (s-chain r←b prf _ kc) (sub-step _ _ (eq-Q x) (B←Q refl refl) (B←Q refl refl)
                                         (sub-step rc₀ rc₁ (eq-B refl) .r←b ext₂ sub)) ext hyp
   = hyp

 transp-𝕂-chain-⊆ : ∀{k o o' r r'}{rc : RecordChainFrom o r}{rc' : RecordChainFrom o' r'}
                → rc ⊆RC rc'
                → 𝕂-chain Contig k rc
                → 𝕂-chain Contig k rc'
 transp-𝕂-chain-⊆ rc⊆rc' 0-chain = 0-chain
 transp-𝕂-chain-⊆ (sub-step .(step rc₀ r←b) .(step rc₁ r←b') (eq-Q refl) _ ext₁
                   (sub-step rc₀ rc₁ (eq-B refl) .r←b r←b' rc⊆rc'))
                (s-chain r←b prf (B←Q _ _) kc) =
    s-chain r←b' (Contig-subst-⊆ kc rc⊆rc' r←b prf) ext₁ (transp-𝕂-chain-⊆ rc⊆rc' kc)

 𝕂-chain-contig : (k : ℕ){o r : Record} → RecordChainFrom o r → Set
 𝕂-chain-contig = 𝕂-chain Contig

 𝕂-chain-to-Simple : ∀{R k r}{rc : RecordChain r} → 𝕂-chain R k rc → 𝕂-chain Simple k rc
 𝕂-chain-to-Simple 0-chain = 0-chain
 𝕂-chain-to-Simple (s-chain r←b prf b←q kc) = s-chain r←b unit b←q (𝕂-chain-to-Simple kc)

 -- Every record chain that ends in a QC is a 𝕂-chain
 to-kchain : ∀{q}(rc : RecordChain (Q q)) → ∃[ k ] (𝕂-chain Simple k rc)
 to-kchain (step (step {B b} rc ()) x@(B←Q _ _))
 to-kchain (step (step {I} rc x₁)   x@(B←Q _ _))
  = 1 , s-chain x₁ unit x 0-chain
 to-kchain (step (step {Q q} rc x₁) x@(B←Q _ _))
  with to-kchain rc
 ...| k , kc = suc k , s-chain x₁ unit x kc

 kchainForget : ∀{P k r}{rc : RecordChain r}(c : 𝕂-chain P k rc) → RecordChain r
 kchainForget {rc = rc} _ = rc

 -- Returns the round of the block heading the k-chain.
 kchainHeadRound : ∀{k r P}{rc : RecordChain r} → 𝕂-chain P k rc → Round
 kchainHeadRound (0-chain {r = r})      = round r
 kchainHeadRound (s-chain r←b _ b←q kk) = kchainHeadRound kk

 kchainBlock : ∀{k o r P}{rc : RecordChainFrom o r} → Fin k → 𝕂-chain P k rc → Block
 kchainBlock zero    (s-chain {b = b} _ _ _ _) = b
 kchainBlock (suc x) (s-chain r←b _ b←q kk)    = kchainBlock x kk

 kchainBlock-toSimple-≡
   : ∀{k r P}{rc : RecordChain r}(x : Fin k)(c : 𝕂-chain P k rc)
   → kchainBlock x (𝕂-chain-to-Simple c) ≡ kchainBlock x c
 kchainBlock-toSimple-≡ zero    (s-chain _ _ _ _)  = refl
 kchainBlock-toSimple-≡ (suc x) (s-chain _ _ _ kk) = kchainBlock-toSimple-≡ x kk

 _b⟦_⟧ : ∀{k o r P}{rc : RecordChainFrom o r} → 𝕂-chain P k rc → Fin k → Block
 chain b⟦ ix ⟧ = kchainBlock ix chain

 kchainBlock-≈RC : ∀{k r r'}{rc : RecordChain r}{rc' : RecordChain r'}
                 → (c3 : 𝕂-chain Contig k rc)(ix : Fin k)
                 → (rc≈rc' : rc ≈RC rc')
                 → c3 b⟦ ix ⟧ ≡ transp-𝕂-chain rc≈rc' c3 b⟦ ix ⟧
 kchainBlock-≈RC 0-chain () _
 kchainBlock-≈RC (s-chain r←b prf (B←Q _ _) kc) ix
                 (eq-step .(step rc₀ r←b) .(step rc₁ r←b') (eq-Q refl) _ ext₁
                   (eq-step rc₀ rc₁ (eq-B refl) .r←b r←b' rc≈rc'))
   with ix
 ...| zero    = refl
 ...| suc ix' = kchainBlock-≈RC kc ix' rc≈rc'

 kchainBlock-⊆RC : ∀{k o o' r r'}{rc : RecordChainFrom o r}{rc' : RecordChainFrom o' r'}
                 → (c3 : 𝕂-chain Contig k rc)(ix : Fin k)
                 → (rc⊆rc' : rc ⊆RC rc')
                 → c3 b⟦ ix ⟧ ≡ transp-𝕂-chain-⊆ rc⊆rc' c3 b⟦ ix ⟧
 kchainBlock-⊆RC 0-chain () _
 kchainBlock-⊆RC (s-chain r←b prf (B←Q _ _) kc) ix
                 (sub-step .(step rc₀ r←b) .(step rc₁ r←b') (eq-Q refl) _ ext₁
                   (sub-step rc₀ rc₁ (eq-B refl) .r←b r←b' rc≈rc'))
   with ix
 ...| zero    = refl
 ...| suc ix' = kchainBlock-⊆RC kc ix' rc≈rc'

 kchainQC : ∀{k r P}{rc : RecordChain r} → Fin k → 𝕂-chain P k rc → QC
 kchainQC zero    (s-chain {q = q} _ _ _ _) = q
 kchainQC (suc x) (s-chain r←b _ b←q kk)    = kchainQC x kk

 kchain-to-RecordChain-at-b⟦⟧
   : ∀{P k r}{rc : RecordChain r}(c : 𝕂-chain P k rc)(ix : Fin k)
   → RecordChain (B (c b⟦ ix ⟧))
 kchain-to-RecordChain-at-b⟦⟧ 0-chain ()
 kchain-to-RecordChain-at-b⟦⟧ (s-chain {rc = rc} r←b x b←q c) zero
   = (step rc r←b)
 kchain-to-RecordChain-at-b⟦⟧ (s-chain r←b x b←q c) (suc zz)
   = kchain-to-RecordChain-at-b⟦⟧ c zz

 kchainBlockRoundZero-lemma
   : ∀{k q P}{rc : RecordChain (Q q)}(c : 𝕂-chain P (suc k) rc)
   → getRound (kchainBlock zero c) ≡ getRound q
 kchainBlockRoundZero-lemma (s-chain r←b prf (B←Q r h) c) = sym r

 kchainBlockRound≤ : ∀{k r P}{rc : RecordChain r}(x y : Fin k)(kc : 𝕂-chain P k rc)
                   → x ≤Fin y → getRound (kchainBlock y kc) ≤ getRound (kchainBlock x kc)
 kchainBlockRound≤ zero zero (s-chain r←b prf b←q kc) hyp = ≤-refl
 kchainBlockRound≤ zero (suc y) (s-chain (Q←B r r←b) prf b←q (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc)) hyp
   = ≤-trans (kchainBlockRound≤ zero y (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc) z≤n) (<⇒≤ r)
 kchainBlockRound≤ (suc x) (suc y) (s-chain r←b prf b←q kc) (s≤s hyp)
   = kchainBlockRound≤ x y kc hyp

 kchain-round-≤-lemma'
   : ∀{k q}{rc : RecordChain (Q q)}(c3 : 𝕂-chain Contig k rc)(ix : Fin k)
   → getRound (c3 b⟦ ix ⟧) ≤ getRound q
 kchain-round-≤-lemma' (s-chain r←b x (B←Q refl b←q) c3) zero = ≤-refl
 kchain-round-≤-lemma' (s-chain (I←B prf imp) unit (B←Q refl _) 0-chain) (suc ())
 kchain-round-≤-lemma' (s-chain (Q←B prf imp) x (B←Q refl _) c2) (suc ix)
   = ≤-trans (kchain-round-≤-lemma' c2 ix) (<⇒≤ prf)

 rc-←-maxRound : ∀{r r'}(rc : RecordChain r') → r ∈RC rc → round r ≤ round r'
 rc-←-maxRound rc here                 = ≤-refl
 rc-←-maxRound rc (transp n x)         = rc-←-maxRound _ n
 rc-←-maxRound .(step _ p) (there p n) = ≤-trans (rc-←-maxRound _ n) (←-round-≤ p)

 kchainBlock-correct
   : ∀{P k q b}{rc : RecordChain (B b)}{b←q : B b ← Q q}
   → (kc : 𝕂-chain P k (step rc b←q))
   → (x : Fin k) → (B (kc b⟦ x ⟧)) ∈RC rc
 kchainBlock-correct (s-chain r←b prf b←q kc) zero = here
 kchainBlock-correct (s-chain r←b prf b←q (s-chain r←b₁ prf₁ b←q₁ kc)) (suc x)
   = there r←b (there b←q₁ (kchainBlock-correct (s-chain r←b₁ prf₁ b←q₁ kc) x))

 -- This is an extended form of RecordChain-irrelevance.
 -- Let rc be:
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₙ ← Cₙ
 --
 -- The (c : 𝕂-chain P k rc) is a predicate on the shape
 -- of rc, establishing that it must be of the following shape:
 -- (where consecutive blocks satisfy P)
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₙ₋ₖ ← Cₙ₋ₖ ⋯ ← Bₙ₋₁ ← Cₙ₋₁ ← Bₙ ← Cₙ
 --                           /\             /\            /
 --                     ⋯ P ₋⌟  ⌞₋₋₋₋ P ₋₋₋₋⌟  ⌞₋₋₋₋ P ₋₋₋⌟
 --
 -- This property states that any other RecordChain that contains one
 -- block b of the kchain above, it also contains the prefix of the
 -- kchain leading to b.
 --
 𝕂-chain-∈RC : ∀{r k P}{rc : RecordChain r}
             → (c : 𝕂-chain P k rc)
             → (x y : Fin k)
             → x ≤Fin y
             → {b : Block}(prf : kchainBlock x c ≡ b)
             → (rc₁ : RecordChain (B b))
             → NonInjective-≡-preds (_∈RC-simple rc ∘ B) (_∈RC-simple rc₁ ∘ B) bId ⊎ (B (kchainBlock y c) ∈RC rc₁)
 𝕂-chain-∈RC (s-chain r←b prf b←q c) zero y z≤n refl rc1
   with RecordChain-irrelevant (step (kchainForget c) r←b) rc1
 ...| inj₁ (hb , (xx , yy)) = inj₁ (hb , (there b←q xx , yy))
 ...| inj₂ res  = inj₂ (transp (kchainBlock-correct (s-chain r←b prf b←q c) y) res)
 𝕂-chain-∈RC (s-chain r←b prf b←q c) (suc x) (suc y) (s≤s x≤y) hyp rc1
    with 𝕂-chain-∈RC c x y x≤y hyp rc1
 ...| inj₁ (hb , (c1 , c2)) = inj₁ (hb , (there b←q (there r←b c1) , c2))
 ...| inj₂ cont = inj₂ cont

 -----------------
 -- Commit Rule --

 -- A block (and everything preceeding it) is said to match the commit rule
 -- when the block is the head of a contiguious 3-chain. Here we define an auxiliary
 -- datatype to make definitions more readable.
 data CommitRuleFrom {o r : Record}(rc : RecordChainFrom o r)(b : Block) : Set where
   commit-rule : (c3 : 𝕂-chain Contig 3 rc)
               → b ≡ c3 b⟦ suc (suc zero) ⟧
               → CommitRuleFrom rc b

 CommitRule : ∀{r} → RecordChain r → Block → Set
 CommitRule = CommitRuleFrom

 transp-CR : ∀{b q}{rc rc' : RecordChain (Q q)}
           → rc ≈RC rc'
           → CommitRule rc  b
           → CommitRule rc' b
 transp-CR rc≈rc' (commit-rule c3 x) =
   commit-rule (transp-𝕂-chain rc≈rc' c3)
               (trans x (kchainBlock-≈RC c3 (suc (suc zero)) rc≈rc'))

 crf⇒cr : ∀ {o q b}
        → (rcf : RecordChainFrom o (Q q))
        → (rc : RecordChain (Q q))
        → CommitRuleFrom rcf b
        → NonInjective-≡-preds (_∈RC-simple rcf ∘ B) (_∈RC-simple rc ∘ B) bId ⊎ CommitRule {Q q} rc b
 crf⇒cr rcf rc (commit-rule c3 prf)
   with RecordChainFrom-irrelevant rcf rc ≈Rec-refl
 ...| inj₁ hb = inj₁ hb
 ...| inj₂ (inj₁ rcf⊆rc) = inj₂ (commit-rule (transp-𝕂-chain-⊆ rcf⊆rc c3)
                                             (trans prf (kchainBlock-⊆RC c3 (suc (suc zero)) rcf⊆rc)))
 ...| inj₂ (inj₂ rc⊆rcf)
   with ≈RC-sym (RecordChain-glb rc⊆rcf)
 ...| rcf≈rc
   with ≈RC-head rcf≈rc
 ...| eq-I = inj₂ (transp-CR rcf≈rc (commit-rule c3 prf))


 vote≡⇒QPrevId≡ : {q q' : QC} {v v' : Vote}
                → v  ∈ qcVotes q
                → v' ∈ qcVotes q'
                → v ≡ v'
                → qCertBlockId q ≡ qCertBlockId q'
 vote≡⇒QPrevId≡ {q} {q'} v∈q v'∈q' refl
     with witness v∈q (qVotes-C2 q) | witness v'∈q' (qVotes-C2 q')
 ... | refl | refl = refl

 vote≡⇒QRound≡ : {q q' : QC} {v v' : Vote}
               → v  ∈ qcVotes q
               → v' ∈ qcVotes q'
               → v ≡ v'
               → getRound q ≡ getRound q'
 vote≡⇒QRound≡ {q} {q'} v∈q v'∈q' refl
     with witness v∈q (qVotes-C3 q) | witness v'∈q' (qVotes-C3 q')
 ... | refl | refl = refl

 ¬bRound≡0 : ∀{b} → RecordChain (B b) → ¬ (getRound b ≡ 0)
 ¬bRound≡0 (step s (I←B ()  h)) refl
 ¬bRound≡0 (step s (Q←B () h)) refl
