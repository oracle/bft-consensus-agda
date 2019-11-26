open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

module LibraBFT.Abstract.RecordStoreState.Invariants 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec : EpochConfig) 
  where

  open import LibraBFT.Abstract.BFT              ec
  open import LibraBFT.Abstract.Records          ec 
  open        WithCryptoHash                     hash hash-cr
  open import LibraBFT.Abstract.Records.Extends  hash hash-cr ec
  open import LibraBFT.Abstract.RecordChain      hash hash-cr ec
  open import LibraBFT.Abstract.RecordStoreState hash hash-cr ec

  -- Now, we need to state the invariants over the system that we seek to:
  --
  --  1) Guarantee when implementing the algo
  --  2) Use on the proofs
  --
  module _ {a}{RSS : Set a}(st : CurrRecordStoreState RSS) where

    open WithRSS st

    -- Correctness of a pool of records is modeled by being able
    -- to trace any record in the chain back to the initial 
    -- record using only records in the pool.
    Correct : Set₁
    Correct = (r : Record) → IsInPool r → RecordChain r

    -- The increasing round rule says that a current RecordStoreState
    -- that contains two votes from α is guaranteed to have the order of
    -- votes respect the rounds
    IncreasingRoundRule : Set₁
    IncreasingRoundRule 
       = (α : Author ec) → Honest α
       → ∀{q q'}(va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → vOrder (∈QC-Vote q va) < vOrder (∈QC-Vote q' va')
       → qRound (qBase q) < qRound (qBase q')

    -- Another important predicate of a "valid" RecordStoreState is the fact
    -- that α's n-th vote is always the same.
    VotesOnlyOnceRule : Set₁
    VotesOnlyOnceRule 
       = (α : Author ec) → Honest α
       → ∀{q q'}(va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → vOrder (∈QC-Vote q va) ≡ vOrder (∈QC-Vote q' va')
       → ∈QC-Vote q va ≡ ∈QC-Vote q' va'

    -- TODO: change parameters to ∈QC-Vote; author can be implicit; QC has to be explicit.
    -- TOEXPLAIN: prevRound is defined for blocks only on the paper; however,
    --            it is cumbersome to open rc' to expose the block that comes
    --            before (Q q'). Yet, (Q q') is valid so said block has the same round,
    --            so, the prevRound (Q q') is the prevRound of the block preceding (Q q').
    LockedRoundRule : Set₁
    LockedRoundRule
      = ∀{R}(α : Author ec) → Honest α
      → ∀{q}{rc : RecordChain (Q q)}{n : ℕ}(c2 : 𝕂-chain R (2 + n) rc)
      → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail.
      → ∀{q'}(rc' : RecordChain (Q q'))
      → (vα' : α ∈QC q')
      → vOrder (∈QC-Vote q vα) < vOrder (∈QC-Vote q' vα')
      → bRound (kchainBlock (suc zero) c2) ≤ prevRound rc'
