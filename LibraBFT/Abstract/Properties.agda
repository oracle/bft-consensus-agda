{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

-- For each desired property (VotesOnce and LockedRoundRule), we have a
-- module containing a Type that defines a property that an implementation
-- should prove, and a proof that it implies the corresponding rule used by
-- the abstract proofs.  Then, we use those proofs to instantiate thmS5,
-- and the use thmS5 to prove a number of correctness conditions.
--
-- TODO-1: refactor this file to separate the definitions and proofs of
-- VotesOnce and LockedRoundRule from their use in proving the correctness
-- properties.

module LibraBFT.Abstract.Properties
  (𝓔 : EpochConfig)(𝓔-valid : ValidEpoch 𝓔)
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (𝓥      : VoteEvidence 𝓔 UID)
  where

 open import LibraBFT.Abstract.Records 𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.Records.Extends 𝓔 UID _≟UID_ 𝓥
 open import LibraBFT.Abstract.RecordChain 𝓔 UID _≟UID_ 𝓥
 import LibraBFT.Abstract.RecordChain.Invariants 𝓔 𝓔-valid UID _≟UID_ 𝓥
   as StaticInv
 open import LibraBFT.Abstract.System 𝓔 UID _≟UID_ 𝓥

 open import LibraBFT.Abstract.BFT 𝓔 𝓔-valid UID _≟UID_ 𝓥

 open EpochConfig 𝓔
 open ValidEpoch 𝓔-valid

 -------------------
 -- * VotesOnce * --
 -------------------

 module VotesOnce {ℓ}(𝓢 : AbsSystemState ℓ) where
  open AbsSystemState 𝓢

  Type : Set ℓ
  Type = ∀{α v v'}
       → Meta-Honest-Member 𝓔 α
       → vMember v  ≡ α → HasBeenSent v
       → vMember v' ≡ α → HasBeenSent v'
       → vRound v ≡ vRound v'
       → vBlockUID v ≡ vBlockUID v'
       -- NOTE: It is interesting that this does not require the timeout signature (or even
       -- presence/lack thereof) to be the same.  The abstract proof goes through without out it, so I
       -- am leaving it out for now, but I'm curious what if anything could go wrong if an honest
       -- author can send different votes for the same epoch and round that differ on timeout
       -- signature.  Maybe something for liveness?

  proof : Type → StaticInv.VotesOnlyOnceRule 𝓢
  proof glob-inv α hα {q} {q'} q∈sys q'∈sys va va' VO≡
     with ∈QC⇒HasBeenSent q∈sys  hα va
        | ∈QC⇒HasBeenSent q'∈sys hα va'
  ...| sent-cv | sent-cv'
     with glob-inv hα (sym (∈QC-Member q  va))  sent-cv
                      (sym (∈QC-Member q' va')) sent-cv'
                      VO≡
  ...| bId≡
     = Vote-η VO≡ (trans (sym (∈QC-Member q va)) (∈QC-Member q' va'))
                  bId≡

 ---------------------
 -- * LockedRound * --
 ---------------------

 -- The LockedRound rule is a little more involved to be expressed in terms
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
 module LockedRound {ℓ}(𝓢 : AbsSystemState ℓ) where
  open AbsSystemState 𝓢

  record voteExtends (v : Vote) : Set where
    constructor mkVE
    field
      veBlock   : Block
      veId      : vBlockUID v ≡ bId    veBlock
      veRounds≡ : vRound    v ≡ bRound veBlock
  open voteExtends

  record Cand-3-chain-vote (v : Vote) : Set where
    field
      votesForB : voteExtends v
      qc        : QC
      qc←b      : Q qc ← B (veBlock votesForB)
      rc        : RecordChain (Q qc)
      n         : ℕ
      is-2chain : 𝕂-chain Simple (2 + n) rc
  open Cand-3-chain-vote public

  -- Returns the round of the head of the candidate 3-chain. In the diagram
  -- explaining Cand-3-chain-vote, this would be v.grandparent.round.
  Cand-3-chain-head-round : ∀{v} → Cand-3-chain-vote v → Round
  Cand-3-chain-head-round c3cand =
    getRound (kchainBlock (suc zero) (is-2chain c3cand))

  -- The locked round rule states a fact about the /previous round/
  -- of a vote; that is, the round of the parent of the block
  -- being voted for; the implementation will have to
  -- show it can construct this parent.
  data VoteParentData-BlockExt : Record → Set where
    vpParent≡I : VoteParentData-BlockExt I
    vpParent≡Q : ∀{b q} → B b ← Q q → VoteParentData-BlockExt (Q q)

  -- TODO-2: it may be cleaner to specify this as a RC 2 vpParent vpQC,
  -- and we should consider it once we address the issue in
  -- Abstract.RecordChain (below the definition of transp-𝕂-chain)

  record VoteParentData (v : Vote) : Set where
    field
      vpExt        : voteExtends v
      vpParent     : Record
      vpExt'       : vpParent ← B (veBlock vpExt)
      vpMaybeBlock : VoteParentData-BlockExt vpParent
  open VoteParentData public

  -- The setup for LockedRoundRule is like thta for VotesOnce.
  -- Given two votes by an honest author α:
  Type : Set ℓ
  Type = ∀{α v v'}
       → Meta-Honest-Member 𝓔 α
       → vMember v  ≡ α → (hbs  : HasBeenSent v)
       → vMember v' ≡ α → (hbs' : HasBeenSent v')
       -- If v is a vote on a candidate 3-chain, that is, is a vote on a block
       -- that extends a 2-chain,
       → (c2 : Cand-3-chain-vote v)
       -- and the round of v is lower than that of v',
       → vRound v < vRound v'
       ------------------------------
       -- then α obeyed the locked round rule:
       → Σ (VoteParentData v')
           (λ vp → Cand-3-chain-head-round c2 ≤ round (vpParent vp))

  private
   make-cand-3-chain : ∀{n R α q}{rc : RecordChain (Q q)}
                     → (c3 : 𝕂-chain R (3 + n) rc)
                     → (v  : α ∈QC q)
                     → Cand-3-chain-vote (∈QC-Vote q v)
   make-cand-3-chain {q = q} (s-chain {suc (suc n)} {rc = rc} {b = b} ext₀@(Q←B h0 refl) _ ext₁@(B←Q h1 refl) c2) v
     with c2
   ...| (s-chain {q = q₀} _ _ _ (s-chain _ _ _ c))
       = record { votesForB = mkVE b (All-lookup (qVotes-C3 q) (Any-lookup-correct v))
                                      (trans (All-lookup (qVotes-C4 q) (Any-lookup-correct v)) h1)
                ; qc = q₀
                ; qc←b = ext₀
                ; rc = rc
                ; n  = n
                ; is-2chain = 𝕂-chain-to-Simple c2
                }

   -- It is important that the make-cand-3-chain lemma doesn't change the head of
   -- the 3-chain/cand-2-chain.
   make-cand-3-chain-lemma
     : ∀{n R α q}{rc : RecordChain (Q q)}
     → (c3 : 𝕂-chain R (3 + n) rc)
     → (v  : α ∈QC q)
     → NonInjective-≡ bId ⊎ kchainBlock (suc zero) (is-2chain (make-cand-3-chain c3 v)) ≡ kchainBlock (suc (suc zero)) c3
   make-cand-3-chain-lemma {q = q} c3@(s-chain {suc (suc n)} {rc = rc} {b = b} ext₀@(Q←B h0 refl) _ ext₁@(B←Q h1 refl) c2) v
     with (veBlock (Cand-3-chain-vote.votesForB (make-cand-3-chain c3 v))) ≟Block b
   ...| no neq = inj₁ ((veBlock (Cand-3-chain-vote.votesForB (make-cand-3-chain c3 v)) , b)
                      , neq
                      , trans (sym (veId (votesForB (make-cand-3-chain c3 v))))
                              (All-lookup (qVotes-C3 q) (∈QC-Vote-correct q v)))
   ...| yes b≡
     with c2
   ...| (s-chain {q = q₀} _ _ _ (s-chain _ _ _ c)) rewrite b≡ = inj₂ refl

   vdParent-prevRound-lemma
      : ∀{α q}(rc : RecordChain (Q q))(va : α ∈QC q)
      → (vp : VoteParentData (∈QC-Vote q va))
      → NonInjective-≡ bId ⊎ (round (vpParent vp) ≡ prevRound rc)
   vdParent-prevRound-lemma {q = q} (step {r = B b} (step rc y) x@(B←Q refl refl)) va vp
     with b ≟Block (veBlock (vpExt vp))
   ...| no imp = inj₁ ( (b , veBlock (vpExt vp))
                      , (imp , id-B∨Q-inj (cong id-B∨Q (trans (sym (All-lookup (qVotes-C3 q) (∈QC-Vote-correct q va)))
                                                               (veId (vpExt vp))))))
   ...| yes refl
     with ←-inj y (vpExt' vp)
   ...| bSameId'
     with y | vpExt' vp
   ...| I←B y0 y1   | I←B e0 e1   = inj₂ refl
   ...| Q←B y0 refl | Q←B e0 refl
     with vpMaybeBlock vp
   ...| vpParent≡Q {b = bP} bP←qP
     with rc
   ...| step {r = B b'} rc' b←q
     with b' ≟Block bP
   ...| no  imp = inj₁ ((b' , bP) , imp , id-B∨Q-inj (lemmaS1-2 (eq-Q refl) b←q bP←qP))
   ...| yes refl
     with bP←qP | b←q
   ...| B←Q refl refl | B←Q refl refl = inj₂ refl

  -- Finally, we can prove the locked round rule from the global version;
  proof : Type → StaticInv.LockedRoundRule 𝓢
  proof glob-inv α hα {q} {q'} q∈sys q'∈sys c3 va rc' va' hyp
    with ∈QC⇒HasBeenSent q∈sys  hα va
       | ∈QC⇒HasBeenSent q'∈sys hα va'
  ...| sent-cv | sent-cv'
    with make-cand-3-chain c3  va | inspect
        (make-cand-3-chain c3) va
  ...| cand | [ R ]
    with glob-inv hα
           (sym (∈QC-Member q  va )) sent-cv
           (sym (∈QC-Member q' va')) sent-cv'
           cand hyp
  ...| va'Par , res
    with vdParent-prevRound-lemma rc' va' va'Par
  ...| inj₁ hb    = inj₁ hb
  ...| inj₂ final
    with make-cand-3-chain-lemma c3 va
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ xx = inj₂ (subst₂ _≤_
          (cong bRound (trans (cong (kchainBlock (suc zero) ∘ is-2chain) (sym R)) xx))
          final
          res)

 -----------------------------------------------------
 -- * The invariants above form a /ValidSysState/ * --
 -----------------------------------------------------

 record ValidSysState {ℓ}(𝓢 : AbsSystemState ℓ) : Set (ℓ+1 ℓ0 ℓ⊔ ℓ) where
   field
     vss-votes-once   : VotesOnce.Type       𝓢
     vss-locked-round : LockedRound.Type     𝓢
 open ValidSysState public

 -- And a valid system state offers the desired /CommitsDoNotConflict/ property
 -- and variants.
 module _ {ℓ}(𝓢 : AbsSystemState ℓ) (st-valid : ValidSysState 𝓢) where
   open AbsSystemState 𝓢
   import LibraBFT.Abstract.RecordChain.Properties 𝓔 𝓔-valid UID _≟UID_ 𝓥 as Props

   CommitsDoNotConflict : ∀{q q'}
        → {rc  : RecordChain (Q q)}  → All-InSys 𝓢 rc
        → {rc' : RecordChain (Q q')} → All-InSys 𝓢 rc'
        → {b b' : Block}
        → CommitRule rc  b
        → CommitRule rc' b'
        → NonInjective-≡ bId ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc)
   CommitsDoNotConflict = Props.WithInvariants.thmS5 𝓢
     (VotesOnce.proof   𝓢 (vss-votes-once st-valid))
     (LockedRound.proof 𝓢 (vss-locked-round st-valid))

   -- When we are dealing with a /Complete/ AbsSystem, we can go a few steps
   -- further and prove that commits do not conflict even if we have only partial
   -- knowledge about Records represented in the system.
   module _ (∈QC⇒AllSent : Complete 𝓢) where

    -- For a /complete/ system we can go even further; if we have evidence that
    -- only the tip of the record chains is in the system, we can infer
    -- the rest of it is also in the system (or blockIDs are not injective).
    CommitsDoNotConflict'
      : ∀{q q'}{rc  : RecordChain (Q q)}{rc' : RecordChain (Q q')}{b b' : Block}
      → InSys (Q q) → InSys (Q q')
      → CommitRule rc  b
      → CommitRule rc' b'
      → NonInjective-≡ bId ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc)
    CommitsDoNotConflict' {q} {q'} {step {r = B bb} rc b←q} {step {r = B bb'} rc' b←q'} {b} {b'} q∈sys q'∈sys cr cr'
       with lemmaB1 q q'
    ...| α , α∈q , α∈q' , hα
       with ∈QC⇒HasBeenSent q∈sys hα α∈q | ∈QC⇒HasBeenSent q'∈sys hα α∈q'
    ...| evs | evs'
       with ∈QC⇒AllSent {q = q} hα α∈q evs | ∈QC⇒AllSent {q = q'} hα α∈q' evs'
    ...| ab , ab←q , arc , ais | ab' , ab←q' , arc' , ais'
       with RecordChain-irrelevant (step arc  ab←q)  (step rc  b←q) |
            RecordChain-irrelevant (step arc' ab←q') (step rc' b←q')
    ...| inj₁ hb     | _       = inj₁ hb
    ...| inj₂ _      | inj₁ hb = inj₁ hb
    ...| inj₂ arc≈rc | inj₂ arc'≈rc'
       with CommitsDoNotConflict
                 (All-InSys-step 𝓢 ais  ab←q  q∈sys )
                 (All-InSys-step 𝓢 ais' ab←q' q'∈sys)
                 (transp-CR (≈RC-sym arc≈rc  ) cr )
                 (transp-CR (≈RC-sym arc'≈rc') cr')
    ...| inj₁ hb = inj₁ hb
    ...| inj₂ (inj₁ b∈arc') = inj₂ (inj₁ (transp-B∈RC arc'≈rc' b∈arc'))
    ...| inj₂ (inj₂ b'∈arc) = inj₂ (inj₂ (transp-B∈RC arc≈rc   b'∈arc))

    -- The final property is even stronger; it states that even if an observer
    -- has access only to suffixes of record chains that match the commit rule,
    -- we can still guarantee that b and b' are non-conflicting blocks.  This
    -- will be important for showing that observers can have confidence in commit
    -- messages without participating in the protocol and without having access to
    -- all previously sent records.
    CommitsDoNotConflict''
      : ∀{o o' q q'}
      → {rcf  : RecordChainFrom o  (Q q)}
      → {rcf' : RecordChainFrom o' (Q q')}
      → {b b' : Block}
      → InSys (Q q)
      → InSys (Q q')
      → CommitRuleFrom rcf  b
      → CommitRuleFrom rcf' b'
      → NonInjective-≡ bId ⊎ Σ (RecordChain (Q q')) ((B b)  ∈RC_)
                           ⊎ Σ (RecordChain (Q q))  ((B b') ∈RC_)
    CommitsDoNotConflict'' {cb} {q = q} {q'} {rcf} {rcf'} q∈sys q'∈sys crf crf'
      with lemmaB1 q q'
    ...| α , α∈q , α∈q' , hα
          with ∈QC⇒HasBeenSent q∈sys hα α∈q | ∈QC⇒HasBeenSent q'∈sys hα α∈q'   -- TODO-1: DRY fail, see proof for Commitsdonotconflict' above
    ...| evs | evs'
       with ∈QC⇒AllSent {q = q} hα α∈q evs | ∈QC⇒AllSent {q = q'} hα α∈q' evs'
    ...| ab , ab←q , arc , ais | ab' , ab←q' , arc' , ais'
       with step arc  ab←q | step arc' ab←q'
    ...| rcq | rcq'
       with crf⇒cr rcf  rcq  crf | crf⇒cr rcf' rcq' crf'
    ...| inj₁ hb | _       = inj₁ hb
    ...| inj₂ _  | inj₁ hb = inj₁ hb
    ...| inj₂ cr | inj₂ cr'
       with CommitsDoNotConflict' q∈sys q'∈sys cr cr'
    ...| inj₁ hb = inj₁ hb
    ...| inj₂ (inj₁ b∈arc') = inj₂ (inj₁ (rcq' , b∈arc'))
    ...| inj₂ (inj₂ b'∈arc) = inj₂ (inj₂ (rcq  , b'∈arc))
