{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Abstract.Types
open import LibraBFT.Abstract.Types.EpochConfig
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open        WithAbsVote

-- For each desired property (VotesOnce and PreferredRoundRule), we have a
-- module containing a Type that defines a property that an implementation
-- should prove, and a proof that it implies the corresponding rule used by
-- the abstract proofs.  Then, we use those proofs to instantiate thmS5,
-- and the use thmS5 to prove a number of correctness conditions.
--
-- TODO-1: refactor this file to separate the definitions and proofs of
-- VotesOnce and PreferredRoundRule from their use in proving the correctness
-- properties.

module LibraBFT.Abstract.Properties
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (NodeId : Set)
  (𝓔  : EpochConfig UID NodeId)
  (𝓥  : VoteEvidence UID NodeId 𝓔)
  where

 open import LibraBFT.Abstract.Records                 UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.Records.Extends         UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.RecordChain             UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.RecordChain.Assumptions UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.System                  UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Abstract.RecordChain.Properties  UID _≟UID_ NodeId 𝓔 𝓥
 open        EpochConfig 𝓔

 module WithAssumptions {ℓ}
   (InSys               : Record → Set ℓ)
   (no-collisions-InSys : NoCollisions InSys)
   (votes-once          : VotesOnlyOnceRule InSys)
   (preferred-round     : PreferredRoundRule InSys)
  where

   open All-InSys-props InSys

   CommitsDoNotConflict : ∀{q q'}
        → {rc  : RecordChain (Q q)}  → All-InSys rc
        → {rc' : RecordChain (Q q')} → All-InSys rc'
        → {b b' : Block}
        → CommitRule rc  b
        → CommitRule rc' b'
        → (B b) ∈RC rc' ⊎ (B b') ∈RC rc
   CommitsDoNotConflict ais ais' cr cr'
      with WithInvariants.thmS5 InSys votes-once preferred-round ais ais' cr cr'
       -- We use the implementation-provided evidence that Block ids are injective among
       -- Block actually in the system to dismiss the first possibility
   ...| inj₁ ((_ , neq , h≡) , (is1 , is2)) = ⊥-elim (neq (no-collisions-InSys is1 is2 h≡))
   ...| inj₂ corr = corr

   -- When we are dealing with a /Complete/ InSys predicate, we can go a few steps
   -- further and prove that commits do not conflict even if we have only partial
   -- knowledge about Records represented in the system.
   module _ (∈QC⇒AllSent : Complete InSys) where

    -- For a /complete/ system (i.e., one in which peers vote for a Block only if
    -- they know of a RecordChain up to that Block whose Records are all InSys), we
    -- can prove that CommitRules based on RecordChainFroms similarly do not
    -- conflict, provided all of the Records in the RecordChainFroms are InSys.
    -- This enables peers not participating in consensus to confirm commits even if
    -- they are sent only a "commit certificate" that contains enough of a
    -- RecordChain to confirm the CommitRule.  Note that it is this "sending" that
    -- justfies the assumption that the RecordChainFroms on which the CommitRules
    -- are based are All-InSys.
    CommitsDoNotConflict'
      : ∀{o o' q q'}
      → {rcf  : RecordChainFrom o  (Q q)}  → All-InSys rcf
      → {rcf' : RecordChainFrom o' (Q q')} → All-InSys rcf'
      → {b b' : Block}
      → CommitRuleFrom rcf  b
      → CommitRuleFrom rcf' b'
      → Σ (RecordChain (Q q')) ((B b)  ∈RC_)
      ⊎ Σ (RecordChain (Q q))  ((B b') ∈RC_)
    CommitsDoNotConflict' {cb} {q = q} {q'} {rcf} rcfAll∈sys {rcf'} rcf'All∈sys crf crf'
       with bft-assumption (qVotes-C1 q) (qVotes-C1 q')
    ...| α , α∈qmem , α∈q'mem , hα
       with Any-sym (Any-map⁻ α∈qmem) | Any-sym (Any-map⁻ α∈q'mem)
    ...| α∈q | α∈q'
       with ∈QC⇒AllSent {q = q} hα α∈q (rcfAll∈sys here) | ∈QC⇒AllSent {q = q'} hα α∈q' (rcf'All∈sys here)
    ...| ab , (arc , ais) , ab←q | ab' , (arc' , ais') , ab←q'
      with crf⇒cr rcf (step arc ab←q) crf | crf⇒cr rcf' (step arc' ab←q') crf'
    ...| inj₁ ((_ , neq , h≡) , (is1 , is2)) | _                     = ⊥-elim (neq (no-collisions-InSys (rcfAll∈sys  is1) (ais  (∈RC-simple-¬here arc  ab←q  (λ ()) is2)) h≡))
    ...| inj₂ _                | inj₁ ((_ , neq , h≡) , (is1 , is2)) = ⊥-elim (neq (no-collisions-InSys (rcf'All∈sys is1) (ais' (∈RC-simple-¬here arc' ab←q' (λ ()) is2)) h≡))
    ...| inj₂ cr               | inj₂ cr'
      with CommitsDoNotConflict (All-InSys-step ais ab←q (rcfAll∈sys here)) (All-InSys-step ais' ab←q' (rcf'All∈sys here)) cr cr'
    ...| inj₁ b∈arc' = inj₁ (step arc' ab←q' , b∈arc')
    ...| inj₂ b'∈arc = inj₂ (step arc  ab←q  , b'∈arc)
