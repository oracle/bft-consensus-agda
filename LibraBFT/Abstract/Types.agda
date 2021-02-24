{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
-- TODO-2: The following import should be eliminated and replaced
-- with the necessary module parameters (PK and MetaHonestPK)
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig

-- This module brings in the base types used through libra
-- and those necessary for the abstract model.
module LibraBFT.Abstract.Types
  (UID    : Set)
  (NodeId : Set)
  (𝓔      : EpochConfig UID NodeId)
  where

  open EpochConfig 𝓔

  -- A member of an epoch is considered "honest" iff its public key is honest.
  Meta-Honest-Member : EpochConfig.Member 𝓔 → Set
  Meta-Honest-Member α = Meta-Honest-PK (getPubKey α)

  -- Naturally, if two witnesses that two authors belong
  -- in the epoch are the same, then the authors are also the same.
  --
  -- This proof is very Galois-like, because of the way we structured
  -- our partial isos. It's actually pretty nice! :)
  member≡⇒author≡ : ∀{α β}
                  → (authorα : Is-just (isMember? α))
                  → (authorβ : Is-just (isMember? β))
                  → to-witness authorα ≡ to-witness authorβ
                  → α ≡ β
  member≡⇒author≡ {α} {β} a b prf
    with isMember? α | inspect isMember? α
  ...| nothing | [ _ ] = ⊥-elim (maybe-any-⊥ a)
  member≡⇒author≡ {α} {β} (just _) b prf
     | just ra | [ RA ]
    with isMember? β | inspect isMember? β
  ...| nothing | [ _ ] = ⊥-elim (maybe-any-⊥ b)
  member≡⇒author≡ {α} {β} (just _) (just _) prf
     | just ra | [ RA ]
     | just rb | [ RB ]
     = trans (sym (author-nodeid-id RA))
             (trans (cong toNodeId prf)
                    (author-nodeid-id RB))

  -- The abstract model is connected to the implementaton by means of
  -- 'VoteEvidence'. The record module will be parameterized by a
  -- v of type 'VoteEvidence 𝓔 UID'; this v will provide evidence
  -- that a given author voted for a given block (identified by the UID)
  -- on the specified round.
  --
  -- When it comes time to instantiate the v above concretely, it will
  -- be something that states that we have a signature from the specified
  -- author voting for the specified block.
  record AbsVoteData : Set where
    constructor mkAbsVoteData
    field
      abs-vRound     : Round
      abs-vMember    : EpochConfig.Member 𝓔
      abs-vBlockUID  : UID
  open AbsVoteData public

  AbsVoteData-η : ∀ {r1 r2 : Round} {m1 m2 : Member} {b1 b2 : UID}
                → r1 ≡ r2
                → m1 ≡ m2
                → b1 ≡ b2
                → mkAbsVoteData r1 m1 b1 ≡ mkAbsVoteData r2 m2 b2
  AbsVoteData-η refl refl refl = refl

  VoteEvidence : Set₁
  VoteEvidence = AbsVoteData → Set
