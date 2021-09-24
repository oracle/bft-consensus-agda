{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

-- This module will in future provide machinery for tracking hash collisions, showing that they
-- exist in a particular ReachableSystemState (that they exist at all is not interesting, they
-- obviously do by the pigeonhole principle; what is interesting is that the properties we want hold
-- unless a hash collision exists within an execution up to some ReachableSystemState.  For
-- convenience while working on proofs, for now we simply postulate that hash collsions do not exist
-- in any ReachableSystemState.

module LibraBFT.ImplShared.Util.HashCollisions
  (iiah  : SystemInitAndHandlers ℓ-RoundManager ConcSysParms)
  where

  open WithInitAndHandlers iiah

  module PerReachableState {st} (r : ReachableSystemState st) where

    -- Note that we do not need to capture all ways in which a ByteString might be represented,
    -- only those for which our proofs require injectivity properties.  Initially, we are
    -- interested only in hash collisions for blockIds.

    data _∈Block_ : BSL → Block → Set where
      inB : ∀ {b} → blockData-bsl (b ^∙ bBlockData) ∈Block b

    data _∈ProposalMsg_ (bsl : BSL) (pm : ProposalMsg) : Set where
      inPM : bsl ∈Block (pm ^∙ pmProposal) → bsl ∈ProposalMsg pm

    data _∈nm (bsl : BSL) : Set where
      inP : ∀ {sndr pm} → (sndr , P pm) ∈ msgPool st → bsl ∈ProposalMsg pm → bsl ∈nm

    -- We could refine this further (∈BlockTree, ∈btIdToBlock), but I don't think we need to.
    data _∈BS_ (bsl : BSL) (bs : BlockStore) : Set where
      inBS : ∀ {eb} → (getBlock (hashBSL bsl) bs ≡ just eb) → bsl ∈Block (eb ^∙ ebBlock) → bsl ∈BS bs

    data _∈RM_ (bsl : BSL) (rm : RoundManager) : Set where
      inRM : bsl ∈BS (rm ^∙ lBlockStore) → bsl ∈RM rm

    -- This amounts to an assumption that the sender of nm (which might be a cheat step) is unable
    -- to find a hash collision with data already represented in the system, and also that an
    -- honest peer executing a handler is unable to find a hash collision with something already
    -- in a peer state or a message sent previously.  We could take it back further and express it
    -- more explicitly as such.

    data HashCollisionFound : Set where
      msgRmHC : ∀ {bs1 bs2 pid}
              → bs1 ∈nm
              → initialised st pid ≡ initd
              → bs2 ∈RM (peerStates st pid)
              → hashBSL bs1 ≡ hashBSL bs2
              → bs1 ≢ bs2
              → HashCollisionFound

    postulate
      meta-specific-cr : ¬ HashCollisionFound

    -- TODO-3: Remove this postulate when we are satisfied with the
    -- "hash-collision-tracking" solution. For example, when proving voo
    -- (in LibraBFT.LibraBFT.Concrete.Properties.VotesOnce), we
    -- currently use this postulate to eliminate the possibility of two
    -- votes that have the same signature but different VoteData
    -- whenever we use sameSig⇒sameVoteData.  To eliminate the
    -- postulate, we need to refine the properties we prove to enable
    -- the possibility of a hash collision, in which case the required
    -- property might not hold.  However, it is not sufficient to simply
    -- prove that a hash collision *exists* (which is obvious,
    -- regardless of the LibraBFT implementation).  Rather, we
    -- ultimately need to produce a specific hash collision and relate
    -- it to the data in the system, so that we can prove that the
    -- desired properties hold *unless* an actual hash collision is
    -- found by the implementation given the data in the system.  In
    -- the meantime, we simply require that the collision identifies a
    -- reachable state; later "collision tracking" will require proof
    -- that the colliding values actually exist in that state.
    postulate  -- temporary assumption that hash collisions don't exist (see comment above)
      meta-sha256-cr : ¬ (NonInjective-≡ sha256)

    sameSig⇒sameVoteDataNoCol : ∀ {v1 v2 : Vote} {pk}
                              → WithVerSig pk v1
                              → WithVerSig pk v2
                              → v1 ^∙ vSignature ≡ v2 ^∙ vSignature
                              → v2 ^∙ vVoteData ≡ v1 ^∙ vVoteData
    sameSig⇒sameVoteDataNoCol {v1} {v2} wvs1 wvs2 refl
       with sameSig⇒sameVoteData {v1} {v2} wvs1 wvs2 refl
    ...| inj₁ hb = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ x = x

