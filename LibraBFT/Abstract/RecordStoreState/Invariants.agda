open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

module LibraBFT.Abstract.RecordStoreState.Invariants 
    {f : ℕ} (ec : EpochConfig f) 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open import LibraBFT.Abstract.Records          ec 
  open        WithCryptoHash                        hash hash-cr
  open import LibraBFT.Abstract.Records.Extends  ec hash hash-cr
  open import LibraBFT.Abstract.RecordChain      ec hash hash-cr
  open import LibraBFT.Abstract.RecordStoreState ec hash hash-cr

  -- Now, we need to state the invariants over the system that we seek to:
  --
  --  1) Guarantee when implementing the algo
  --  2) Use on the proofs
  --
  module _ {a}{RSS : Set a}(curr : isRecordStoreState RSS) where

    open WithRSS curr

    -- Correctness of a pool of records is modeled by bein able
    -- to trace any record in the chain back to the initial 
    -- record using only records in the pool.
    Correct : Set₁
    Correct = {r : Record} → isInPool curr r → RecordChain r

    -- The increasing round rule says that a current RecordStoreState
    -- that contains two votes from α is guaranteed to have the order of
    -- votes respect the rounds
    IncreasingRoundRule : Set₁
    IncreasingRoundRule 
       = (α : Author ec) → Honest {ec = ec} α
       → ∀{q q'}(va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → vOrder (∈QC-Vote q va) < vOrder (∈QC-Vote q' va')
       → qRound q < qRound q' 

    -- Another important predicate of a "valid" RecordStoreState is the fact
    -- that α's n-th vote is always the same.
    VotesOnlyOnceRule : Set₁
    VotesOnlyOnceRule 
       = (α : Author ec) → Honest {ec = ec} α
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
      = (α : Author ec) → Honest {ec = ec} α
      → ∀{q}{rc : RecordChain (Q q)}{n : ℕ}(c2 : 𝕂-chain (2 + n) rc)
      → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail.
      → ∀{q'}(rc' : RecordChain (Q q'))
      → (vα' : α ∈QC q')
      → vOrder (∈QC-Vote q vα) < vOrder (∈QC-Vote q' vα')
      → bRound (kchainBlock (suc zero) c2) ≤ prevRound rc'
