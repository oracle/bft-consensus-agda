{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types.EpochConfig
open        WithAbsVote

-- Here we establish the properties necessary to achieve consensus
-- just like we see them on paper: stating facts about the state of
-- the system and reasoning about which QC's exist in the system.
-- This module is a stepping stone to the properties we want;
-- you should probably not be importing it directly, see 'LibraBFT.Abstract.Properties'
-- instead.
--
-- The module 'LibraBFT.Abstract.Properties' proves that the invariants
-- presented here can be obtained from reasoning about sent votes,
-- which provides a much easier-to-prove interface to an implementation.

module LibraBFT.Abstract.RecordChain.Assumptions
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (NodeId : Set)
    (𝓔      : EpochConfig UID NodeId)
    (𝓥      : VoteEvidence UID NodeId 𝓔)
  where

  open import LibraBFT.Abstract.Types           UID        NodeId 𝓔
  open import LibraBFT.Abstract.System          UID _≟UID_ NodeId 𝓔 𝓥
  open import LibraBFT.Abstract.Records         UID _≟UID_ NodeId 𝓔 𝓥
  open import LibraBFT.Abstract.Records.Extends UID _≟UID_ NodeId 𝓔 𝓥
  open import LibraBFT.Abstract.RecordChain     UID _≟UID_ NodeId 𝓔 𝓥
  open        EpochConfig 𝓔

  module _ {ℓ}(InSys : Record → Set ℓ) where

   -- Another important predicate of a "valid" RecordStoreState is the fact
   -- that α's n-th vote is always the same.
   VotesOnlyOnceRule : Set ℓ
   VotesOnlyOnceRule
      -- Given an honest α
      = (α : Member) → Meta-Honest-Member α
      -- For all system states where q and q' exist,
      → ∀{q q'} → (q∈𝓢 : InSys (Q q)) → (q'∈𝓢 : InSys (Q q'))
      -- such that α voted for q and q'; if α says it's the same vote, then it's the same vote.
      → (v  : α ∈QC q)(v' : α ∈QC q')
      → abs-vRound (∈QC-Vote q v) ≡ abs-vRound (∈QC-Vote q' v')
      -----------------
      → ∈QC-Vote q v ≡ ∈QC-Vote q' v'


  module _ {ℓ}(InSys  : Record → Set ℓ) where

   -- The preferred-round rule (aka locked-round-rule) is a critical
   -- aspect of LibraBFT's correctness. It states that an honest node α will cast
   -- votes for blocks b only if prevRound(b) ≥ preferred_round(α), where preferred_round(α)
   -- is defined as $max { round b | b is the head of a 2-chain }$.
   --
   -- Operationally, α can ensure it obeys this rule as follows: it keeps a counter
   -- preferred_round, initialized at 0 and, whenever α receives a QC q that forms a
   -- 2-chain:
   --
   --  Fig1
   --
   --    I ← ⋯ ← b₁ ← q₁ ← b ← q
   --        ⌞₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋⌟
   --                2-chain
   --
   -- it checks whether round(b₁) , which is the head of the 2-chain above,
   -- is greater than its previously known preferred_round; if so, α updates
   -- it.  Note that α doesn't need to cast a vote in q, above, to have its
   -- preferred_round updated.  All that matters is that α has seen q.
   --
   -- We are encoding the rules governing Libra nodes as invariants in the
   -- state of other nodes. Hence, the PreferredRoundRule below states an invariant
   -- on the state of β, if α respects the preferred-round-rule.
   --
   -- Let the state of β be as below, such that α did cast votes for q
   -- and q' in that order (α is honest here!):
   --
   --
   --  Fig2
   --                            3-chain
   --        ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
   --        |        2-chain            |          α knows of the 2-chain because
   --        ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝        |          it voted at the 3-chain.
   --    I ← ⋯ ← b₂ ← q₂ ← b₁ ← q₁ ← b ← q
   --         ↖
   --           ⋯ ← b₁' ← q₁' ← b' ← q'
   --
   -- Then, since α is honest and follows the preferred-round rule, we know that
   -- round(b₂) ≤ round(b₁') because, by seeing that α voted on q, we know that α
   -- has seen the 2-chain above, hence, α's preferred_round was at least round(b₂) at
   -- the time α cast its vote for b.
   --
   -- After casting a vote for b, α cast a vote for b', which means that α must have
   -- checked that round(b₂) ≤ prevRound(b'), as stated by the preferred round rule.
   --
   -- The invariant below states that, since α is honest, we can trust that these
   -- checks have been performed and we can infer this information solely
   -- by seeing α has knowledge of the 2-chain in Fig2 above.
   --
   PreferredRoundRule : Set ℓ
   PreferredRoundRule
     = ∀(α : Member) → Meta-Honest-Member α
     → ∀{q q'}(q∈𝓢 : InSys (Q q))(q'∈𝓢 : InSys (Q q'))
     → {rc : RecordChain (Q q)}{n : ℕ}(c3 : 𝕂-chain Contig (3 + n) rc)
     → (v : α ∈QC q) -- α knows of the 2-chain because it voted on the tail of the 3-chain!
     → (rc' : RecordChain (Q q'))
     → (v' : α ∈QC q')
     → abs-vRound (∈QC-Vote q v) < abs-vRound (∈QC-Vote q' v')
     → NonInjective-≡ bId ⊎ (getRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound rc')
