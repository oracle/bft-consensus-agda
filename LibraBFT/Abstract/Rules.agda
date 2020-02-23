open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Abstract.Types

-- VCM : I think this module is also obsolete, for the time being.
--       if not; there's a lot of fixing needed here
module LibraBFT.Abstract.Rules
  (mec : Meta EpochConfig)
  (UID : Set) 
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  where

  private
    ec : EpochConfig
    ec = unsafeReadMeta mec

  open import LibraBFT.Abstract.BFT     mec UID _≟UID_
  open import LibraBFT.Abstract.Records mec UID _≟UID_

  ---------------------------------------
  -- Honesty and Dishonesty of Authors --
  --
  -- Sometimes when a participant breaks the rules, it can be proved by another participant,
  -- providing a concrete ACCOUNTABILITY OPPORTUNITY.  In other cases, it may be deteced within a
  -- proof (e.g., based on auxiliary variables such as vOrder that are not available to participant;
  -- in such cases, we can eliminate proof obligations because an assumed-honest participant must
  -- have broken a rule, even though there is no accountability opportunity for participants to use
  -- in practice.  Here we provide the means to eliminate proof obligations for both types of
  -- scenario, keeping them separate to inform concrete implementations about when accountability
  -- opportunities exist.  A couple of examples are included but there will be more.

  data ProvablyDishonest (α : Author ec) : Set where
{-
     same-round-different-votes
       : (sv₀ : {! VerSigned (BVote (Author ec)) !})
       → (sv₁ : {! VerSigned (BVote (Author ec)) !})
       → getEpochId  sv₀ ≡ epochId ec
       → getEpochId  sv₁ ≡ epochId ec
       → getAuthor sv₀ ≡ α
       → getAuthor sv₁ ≡ α
       → getRound  sv₀ ≡ getRound sv₁
       → content   sv₀ ≢ content sv₁
       → ProvablyDishonest α
-}

  data BrokeRule (α : Author ec) : Set where
{-
     -- MSM: DANGER!  I don't think this scenario indicates that α is dishonest.  The two votes could
     -- be the same votes, included in different QCs (possibly constructed by someone *else*
     -- dishonest).  This shows that we'd better be pretty careful with this approach, as it's an
     -- invitation to introduce contradictory postulates (via ACCOUNTABILITY-OPP).
     same-order-diff-qcs-DO-NOT-USE 
       : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
       → q ≢ q'
       → voteOrder (∈QC-Vote q vα) ≡ voteOrder (∈QC-Vote q' vα')
       → BrokeRule α

     -- This one is not an accountability-opp, because the vOrder will not actually be included in
     -- Votes, so nobody can detect this one.  Still, it indiciates Dishonest behavior.
     violates-increasing-round-rule
       : (sv₀ : VerSigned (BVote (Author ec)))
       → (sv₁ : VerSigned (BVote (Author ec)))
       → getEpochId  sv₀ ≡ epochId ec
       → getEpochId  sv₁ ≡ epochId ec
       → getAuthor sv₀ ≡ α
       → getAuthor sv₁ ≡ α
       → vOrder (content sv₀) <VO vOrder (content sv₁)
       → getRound  sv₀ ≥ getRound sv₁   -- TODO: check
       → BrokeRule α

-}
{-- Some other scenarios for which we can construct accountability opportunities or broke-rule
    proofs are:

    - qc-votes-wrong-round

    - qc-votes-sigs-dont-verify

    - qc-wrong-round

    - ...

--}

  postulate
    ACCOUNTABILITY-OPP : ∀{α} → Honest ec α → ProvablyDishonest α → ⊥
    BROKE-RULE         : ∀{α} → Honest ec α → BrokeRule α         → ⊥

