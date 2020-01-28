open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.RecordStoreState.Invariants 
    (ec  : EpochConfig) 
    (UID : B∨QC → Set) 
  where

  open import LibraBFT.Abstract.BFT              ec UID
  open import LibraBFT.Abstract.Records          ec UID
  open import LibraBFT.Abstract.Records.Extends  ec UID
  open import LibraBFT.Abstract.RecordChain      ec UID
  open import LibraBFT.Abstract.RecordStoreState ec UID

  -- Now, we need to state the invariants over the system that we seek to:
  --
  --  1) Guarantee when implementing the algo
  --  2) Use on the proofs
  --
  module _ {a}{RSS : Set a}⦃ isRSS : isRecordStoreState RSS ⦄(curr : RSS) where

    open WithRSS curr

    -- Correctness of a pool of records is modeled by being able
    -- to trace any record in the chain back to the initial 
    -- record using only records in the pool.
    Correct : Set
    Correct = (r : Record) → IsInPool r → RecordChain r

    -- The increasing round rule says that a current RecordStoreState
    -- that contains two votes from α is guaranteed to have the order of
    -- votes respect the rounds
    IncreasingRoundRule : Set
    IncreasingRoundRule 
       = (α : Author ec) → Honest α
       → ∀{q q'} → IsInPool (Q q) → IsInPool (Q q') 
       → (va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → voteOrder (∈QC-Vote q va) <VO voteOrder (∈QC-Vote q' va')
       → getRound q < getRound q'

    -- An honest participant does not vote for two different blocks in the same round.  This is
    -- "implied" by the informal Increasing Round Rule in the paper: "An honest node that voted once
    -- for B in the past may only vote for B' if round(B) < round(B′)", but it is not implied by
    -- our vOrder-based formalization thereof (above).  We therefore capture this requirement via an
    -- additional formal requirement VotesOnlyOnceRule (below).

    -- TODO: the rest of this comment really belongs somewhere else that doesn't exist yet, perhaps
    -- in the Rules module I intend to introduce soon.
    -- For the abstract model, we need this property only between pairs of votes that are in the
    -- pool.  However, for the concrete model to provide proof that the rule is followed to the
    -- abstract model, we will need to state the rule more generally.  We need the property to hold
    -- for all pairs of votes that are signed and sent by an author.  It is tempting to drop the
    -- "and sent" constraint, which rules out the possibility that an honest author could sign *but
    -- not send* contradictory votes for the same round.  This might seem unimportant, but it places
    -- an unncessary constraint on implementations.  For example, one might attempt to optimize an
    -- implementation by initiating signing in one thread while validating conditions in another.
    -- In this case, an honest author might sign a Vote, then decide not to send it, and later sign
    -- a different vote that conflicts with it.

    -- Another important predicate of a "valid" RecordStoreState is the fact
    -- that α's n-th vote is always the same.
    VotesOnlyOnceRule : Set
    VotesOnlyOnceRule 
       = (α : Author ec) → Honest α
       → ∀{q q'} → IsInPool (Q q) → IsInPool (Q q') 
       → (va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → voteOrder (∈QC-Vote q va) ≡ voteOrder (∈QC-Vote q' va')
       → ∈QC-Vote q va ≡ ∈QC-Vote q' va'

    -- TODO: change parameters to ∈QC-Vote; author can be implicit; QC has to be explicit.
    -- TOEXPLAIN: prevRound is defined for blocks only on the paper; however,
    --            it is cumbersome to open rc' to expose the block that comes
    --            before (Q q'). Yet, (Q q') is valid so said block has the same round,
    --            so, the prevRound (Q q') is the prevRound of the block preceding (Q q').
    -- This is in Set₁ because we universally quantify over (Record → Record → Set)
    -- for the relation passed to c2.
    LockedRoundRule : Set₁
    LockedRoundRule
      = ∀{R}(α : Author ec) → Honest α
      → ∀{q}{rc : RecordChain (Q q)}{n : ℕ}(c2 : 𝕂-chain R (2 + n) rc)
      → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail.
      → ∀{q'}(rc' : RecordChain (Q q'))
      → (vα' : α ∈QC q')
      → voteOrder (∈QC-Vote q vα) <VO voteOrder (∈QC-Vote q' vα')
      → getRound (kchainBlock (suc zero) c2) ≤ prevRound rc'
