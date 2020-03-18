open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.RecordStoreState.Invariants 
    (mec  : Meta EpochConfig) 
    (UID : Set) 
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  where

  private
    ec : EpochConfig
    ec = unsafeReadMeta mec

  open import LibraBFT.Abstract.BFT              mec UID _≟UID_
  open import LibraBFT.Abstract.Records          mec UID _≟UID_
  open import LibraBFT.Abstract.Records.Extends  mec UID _≟UID_
  open import LibraBFT.Abstract.RecordChain      mec UID _≟UID_
  open import LibraBFT.Abstract.RecordStoreState mec UID _≟UID_

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
       = (α : Author ec) → Honest ec α
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
       = (α : Author ec) → Honest ec α
       → ∀{q q'} → IsInPool (Q q) → IsInPool (Q q') 
       → (va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → voteOrder (∈QC-Vote q va) ≡ voteOrder (∈QC-Vote q' va')
       → ∈QC-Vote q va ≡ ∈QC-Vote q' va'

    -- The locked-round-rule, or preferred-round rule (from V3 onwards) is a potentially 
    -- confusing aspect of Libra. It states that an honest node α will only cast
    -- votes for blocks b such that prevRound(b) ≥ locked_round(α), where locked_round(α)
    -- is defined as $max { round b | b is the head of a 2-chain }$. 
    -- 
    -- Operationally, α keeps a counter locked_round, initialized at 0 and, whenever
    -- α receives a QC q that forms a 2-chain:
    --
    --  Fig1
    --
    --    I ← ⋯ ← b₁ ← q₁ ← b ← q 
    --            ⌞₋₋₋₋₋₋₋₋₋₋₋₋₋⌟
    --                2-chain
    --
    -- it should check whether round(b₁) , which is the head of the 2-chain above,
    -- is bigger than its previously known locked_round, if it is, α should update it.
    -- Note that α doesnt need to cast a vote in q, above, to have its locked_round updated.
    -- All that matters is that α has seen q.
    --
    -- We are encoding the rules governing Libra nodes as invariants in the
    -- state of other nodes. Hence, the LockedRoundRule below states an invariant
    -- in the state of β, if α respects the locked-round-rule. 
    --
    -- Let the state of β be as below, such that α did cast votes for q
    -- and q' in that order (α is honest here!):
    --
    --
    --  Fig2
    --                            3-chain
    --            ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
    --            |    2-chain            |          α knows of the 2-chain because
    --            ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝        |          it voted at the 3-chain.
    --    I ← ⋯ ← b₂ ← q₂ ← b₁ ← q₁ ← b ← q
    --         ↖ 
    --           ⋯ ← b₁' ← q₁' ← b' ← q'
    --
    -- Then, since α is honest and follows the locked-round rule, we know for sure
    -- that round(b₂) ≤ round(b₁'), thats because by seeing that α voted on q, we
    -- know that α has seen the 2-chain above, hence, α locked_round was at least round(b₂)
    -- at the time α casted its vote for b. 
    --
    -- After casting a vote for b; α casted a vote for b', which means that α must have
    -- checked that round(b₂) ≤ prevRound(b'), as stated by the locked round rule.
    --
    -- The invariant below states that since α is honest, we can trust that these
    -- checks have been performed and we can infer this information solely 
    -- by seeing α has knowledge of te 2-chain in Fig2 above.
    --
    LockedRoundRule : Set₁
    LockedRoundRule
      = ∀{R}(α : Author ec) → Honest ec α
      → ∀{q}{rc : RecordChain (Q q)}{n : ℕ}(c3 : 𝕂-chain R (3 + n) rc)
      → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail of the 3-chain!
      → ∀{q'}(rc' : RecordChain (Q q'))
      → (vα' : α ∈QC q')
      → voteOrder (∈QC-Vote q vα) <VO voteOrder (∈QC-Vote q' vα')
      → getRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound rc'
