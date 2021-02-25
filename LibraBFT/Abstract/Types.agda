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
