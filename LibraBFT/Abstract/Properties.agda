{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
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
 import LibraBFT.Abstract.RecordChain.Assumptions 𝓔 𝓔-valid UID _≟UID_ 𝓥
   as StaticAssumptions
 open import LibraBFT.Abstract.System 𝓔 UID _≟UID_ 𝓥

 open import LibraBFT.Abstract.BFT 𝓔 𝓔-valid UID _≟UID_ 𝓥

 open EpochConfig 𝓔
 open ValidEpoch 𝓔-valid

 module WithAssumptions {ℓ}
   (InSys                 : Record → Set ℓ)
   (votes-only-once       : StaticAssumptions.VotesOnlyOnceRule InSys)
   (locked-round-rule     : StaticAssumptions.LockedRoundRule   InSys)
  where

   open All-InSys-props InSys
   import LibraBFT.Abstract.RecordChain.Properties 𝓔 𝓔-valid UID _≟UID_ 𝓥 as Props

   CommitsDoNotConflict : ∀{q q'}
        → {rc  : RecordChain (Q q)}  → All-InSys rc
        → {rc' : RecordChain (Q q')} → All-InSys rc'
        → {b b' : Block}
        → CommitRule rc  b
        → CommitRule rc' b'
        → NonInjective-≡ bId ⊎ ((B b) ∈RC rc' ⊎ (B b') ∈RC rc)
   CommitsDoNotConflict = Props.WithInvariants.thmS5 InSys votes-only-once locked-round-rule

   -- When we are dealing with a /Complete/ InSys predicate, we can go a few steps
   -- further and prove that commits do not conflict even if we have only partial
   -- knowledge about Records represented in the system.
   module _ (∈QC⇒AllSent : Complete InSys) where

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
       with ∈QC⇒AllSent {q = q} hα α∈q q∈sys | ∈QC⇒AllSent {q = q'} hα α∈q' q'∈sys
    ...| ab , ab←q , arc , ais | ab' , ab←q' , arc' , ais'
       with RecordChain-irrelevant (step arc  ab←q)  (step rc  b←q) |
            RecordChain-irrelevant (step arc' ab←q') (step rc' b←q')
    ...| inj₁ hb     | _       = inj₁ hb
    ...| inj₂ _      | inj₁ hb = inj₁ hb
    ...| inj₂ arc≈rc | inj₂ arc'≈rc'
       with CommitsDoNotConflict
                 (All-InSys-step ais  ab←q  q∈sys )
                 (All-InSys-step ais' ab←q' q'∈sys)
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
       with ∈QC⇒AllSent {q = q} hα α∈q q∈sys | ∈QC⇒AllSent {q = q'} hα α∈q' q'∈sys
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
