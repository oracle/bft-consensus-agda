{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import Util.Lemmas
open import Util.Prelude

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        WithAbsVote

module LibraBFT.Concrete.Obligations.PreferredRound
  (𝓔 : EpochConfig)
  (𝓥 : VoteEvidence 𝓔)
  where
 open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Concrete.Intermediate               𝓔 𝓥

 record VotesForBlock (v : Vote) : Set where
    constructor mkVE
    field
      veBlock   : Block
      veId      : vBlockUID v ≡ bId    veBlock
      veRounds≡ : vRound    v ≡ bRound veBlock
 open VotesForBlock

 module _ {ℓ}(𝓢 : IntermediateSystemState ℓ) where
  open IntermediateSystemState 𝓢
  open All-InSys-props InSys

  ---------------------
  -- * PreferredRound * --
  ---------------------

  -- The PreferredRound rule is a little more involved to be expressed in terms
  -- of /HasBeenSent/: it needs two additional pieces which are introduced
  -- next.

  -- Cand-3-chain v carries the information for estabilishing
  -- that v.proposed will be part of a 3-chain if a QC containing v is formed.
  -- The difficulty is that we can't easily access the "grandparent" of a vote.
  -- Instead, we must explicitly state that it exists.
  --
  --                                candidate 3-chain
  --       +------------------------------------------------------+
  --       |                                                      |
  --       |       2-chain                                        |
  --       +----------------------------------+
  --  ⋯ <- v.grandparent <- q₁ <- v.parent <- q <- v.proposed  <- v
  --                                          ̭
  --                                          |
  --                                     The 'qc' defined below is an
  --                                     abstract view of q, above.
  record Cand-3-chain-vote (v : Vote) : Set ℓ where
     constructor mkCand3chainvote
     field
       votesForB : VotesForBlock v
       c3Blk∈sys : InSys (B (veBlock votesForB))
       qc        : QC
       qc←b      : Q qc ← B (veBlock votesForB)
       rc        : RecordChain (Q qc)
       rc∈sys    : All-InSys rc
       n         : ℕ
       is-2chain : 𝕂-chain Contig (2 + n) rc
  open Cand-3-chain-vote public

  v-cand-3-chain⇒0<roundv : ∀ {v} → Cand-3-chain-vote v → 0 < vRound v
  v-cand-3-chain⇒0<roundv
    record { votesForB = (mkVE veBlock₁ veId₁ refl)
           ; qc = qc
           ; qc←b = qc←b
           ; rc = rc
           ; n = n
           ; is-2chain = is-2chain }
    with qc←b
  ... | Q←B (s≤s x) x₁ = s≤s z≤n

   -- Returns the round of the head of the candidate 3-chain. In the diagram
   -- explaining Cand-3-chain-vote, this would be v.grandparent.round.
  Cand-3-chain-head-round : ∀{v} → Cand-3-chain-vote v → Round
  Cand-3-chain-head-round c3cand =
     getRound (kchainBlock (suc zero) (is-2chain c3cand))

 module _ {ℓ}(𝓢 : IntermediateSystemState ℓ) where
  open IntermediateSystemState 𝓢
  open All-InSys-props InSys

   -- The preferred round rule states a fact about the /previous round/
   -- of a vote; that is, the round of the parent of the block
   -- being voted for; the implementation will have to
   -- show it can construct this parent.
  data VoteParentData-BlockExt : Record → Set ℓ where
     vpParent≡I : VoteParentData-BlockExt I
     vpParent≡Q : ∀{b q} → B b ← Q q → InSys (B b) → VoteParentData-BlockExt (Q q)

   -- TODO-2: it may be cleaner to specify this as a RC 2 vpParent vpQC,
   -- and we should consider it once we address the issue in
   -- Abstract.RecordChain (below the definition of transp-𝕂-chain)

  record VoteParentData (v : Vote) : Set ℓ where
    field
      vpV4B        : VotesForBlock v
      vpBlock∈sys  : InSys (B (veBlock vpV4B))
      vpParent     : Record
      vpParent∈sys : InSys vpParent
      vpExt        : vpParent ← B (veBlock vpV4B)
      vpMaybeBlock : VoteParentData-BlockExt vpParent
  open VoteParentData public

  -- The setup for PreferredRoundRule is like that for VotesOnce.
  -- Given two votes by an honest author α:
  Type : Set ℓ
  Type = ∀{α v v'}
       → Meta-Honest-Member α
       → vMember v  ≡ α → HasBeenSent v
       → vMember v' ≡ α → HasBeenSent v'
       -- If v is a vote on a candidate 3-chain, that is, is a vote on a block
       -- that extends a 2-chain,
       → (c2 : Cand-3-chain-vote 𝓢 v)
       -- and the round of v is lower than that of v',
       → vRound v < vRound v'
       ------------------------------
       -- then α obeyed the preferred round rule:
       → Σ (VoteParentData v')
           (λ vp → Cand-3-chain-head-round 𝓢 c2 ≤ round (vpParent vp))

  private
   make-cand-3-chain : ∀{n α q}{rc : RecordChain (Q q)}
                     → All-InSys rc
                     → (c3 : 𝕂-chain Contig (3 + n) rc)
                     → (v  : α ∈QC q)
                     → Cand-3-chain-vote 𝓢 (∈QC-Vote q v)
   make-cand-3-chain {q = q} ais (s-chain {suc (suc n)} {rc = rc} {b = b} ext₀@(Q←B h0 refl) _ ext₁@(B←Q h1 refl) c2) v
     with c2
   ...| (s-chain {q = q₀} _ _ _ _)
       = record { votesForB = mkVE b (All-lookup (qVotes-C2 q) (Any-lookup-correct v))
                                     (trans (All-lookup (qVotes-C3 q) (Any-lookup-correct v)) h1)
                ; c3Blk∈sys = All-InSys⇒last-InSys (All-InSys-unstep ais)
                ; qc = q₀
                ; qc←b = ext₀
                ; rc = rc
                ; rc∈sys =  All-InSys-unstep (All-InSys-unstep ais)
                ; n  = n
                ; is-2chain = c2
                }

   -- It is important that the make-cand-3-chain lemma doesn't change the head of
   -- the 3-chain/cand-2-chain.
   make-cand-3-chain-lemma
     : ∀{n α q}{rc : RecordChain (Q q)} → (ais : All-InSys rc)
     → (c3 : 𝕂-chain Contig (3 + n) rc)
     → (v  : α ∈QC q)
     → kchainBlock (suc zero) (is-2chain (make-cand-3-chain ais c3 v)) ≡ kchainBlock (suc (suc zero)) c3
   make-cand-3-chain-lemma {q = q} ais₀ c3@(s-chain {suc (suc n)} {rc = rc} {b = b} ext₀@(Q←B h0 refl) _ ext₁@(B←Q h1 refl) c2) v
     with c2
   ...| (s-chain {q = q₀} _ _ _ (s-chain _ _ _ c)) = refl

   vdParent-prevRound-lemma
      : ∀{α q}(rc : RecordChain (Q q)) → (All-InSys rc) → (va : α ∈QC q)
      → (vp : VoteParentData (∈QC-Vote q va))
        -- These properties are still about abstract records, so we could still cook up a trivial
        -- proof.  Therefore, if we need these properties, we need to connect the collision to
        -- Records that are InSys
      → NonInjective-≡-pred (InSys ∘ B) bId ⊎ (round (vpParent vp) ≡ prevRound rc)
   vdParent-prevRound-lemma {q = q} (step {r = B b} (step rc y) x@(B←Q refl refl)) ais va vp
     with b ≟Block (veBlock (vpV4B vp))
   ...| no imp = inj₁ (((b , veBlock (vpV4B vp))
                      , (imp , (id-B∨Q-inj (cong id-B∨Q (trans (sym (All-lookup (qVotes-C2 q) (∈QC-Vote-correct q va)))
                                                               (veId (vpV4B vp)))))))
                      , (ais (there x here) , (vpBlock∈sys vp)))
   ...| yes refl
     with ←-inj y (vpExt vp)
   ...| bSameId'
     with y | vpExt vp
   ...| I←B y0 y1   | I←B e0 e1   = inj₂ refl
   ...| Q←B y0 refl | Q←B e0 refl
     with vpMaybeBlock vp
   ...| vpParent≡Q {b = bP} bP←qP bp∈Sys
     with rc
   ...| step {r = B b'} rc' b←q
     with b' ≟Block bP
   ...| no  imp = inj₁ (((b' , bP)
                       , (imp , (id-B∨Q-inj (lemmaS1-2 (eq-Q refl) b←q bP←qP))))
                       , (ais (there x (there (Q←B y0 refl) (there b←q here)))
                         , bp∈Sys))
   ...| yes refl
     with bP←qP | b←q
   ...| B←Q refl refl | B←Q refl refl = inj₂ refl

  -- Finally, we can prove the preferred round rule from the global version;
  proof : Type → PreferredRoundRule InSys
  proof glob-inv α hα {q} {q'} {rc} ais₀ c3 va {rc'} ais₁ va' hyp
    with All-InSys⇒last-InSys ais₀ | All-InSys⇒last-InSys ais₁
  ...| q∈sys   | q'∈sys
    with ∈QC⇒HasBeenSent q∈sys  hα va
       | ∈QC⇒HasBeenSent q'∈sys hα va'
  ...| sent-cv | sent-cv'
    with make-cand-3-chain ais₀ c3  va | inspect
        (make-cand-3-chain ais₀ c3) va
  ...| cand | [ R ]
    with glob-inv hα
           (sym (∈QC-Member q  va )) sent-cv
           (sym (∈QC-Member q' va')) sent-cv'
           cand hyp
  ...| va'Par , res
    with vdParent-prevRound-lemma rc' ais₁ va' va'Par
  ...| inj₁ hb    = inj₁ hb
  ...| inj₂ final
    with make-cand-3-chain-lemma ais₀ c3 va
  ...| xx = inj₂ (subst₂ _≤_
                   (cong bRound (trans (cong (kchainBlock (suc zero) ∘ is-2chain) (sym R)) xx))
                   final
                   res)

