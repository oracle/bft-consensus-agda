{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System.Parameters
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

