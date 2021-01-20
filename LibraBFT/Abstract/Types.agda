{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- This module brings in the base types used through libra
-- and those necessary for the abstract model.
module LibraBFT.Abstract.Types where

  open import LibraBFT.Base.Types public

  -- Simple way to flag meta-information without having it getting
  -- in the way.
  Meta : ∀{ℓ} → Set ℓ → Set ℓ
  Meta x = x

  -- An epoch-configuration carries only simple data about the epoch; the complicated
  -- parts will be provided by the System, defined below.
  --
  -- The reason for the separation is that we should be able to provide
  -- an EpochConfig from a single peer state.
  record EpochConfig : Set where
    constructor mkEpochConfig
    field
      -- TODO-2 : This should really be a UID as Hash should not show up in the Abstract namespace.
      -- This will require some refactoring of modules and reordering of module parameters.
      initialAgreedHash : Hash
      epochId   : EpochId
      authorsN  : ℕ
      bizF      : ℕ
      isBFT     : authorsN ≥ suc (3 * bizF)

    QSize : ℕ
    QSize = authorsN ∸ bizF

    -- The set of members of this epoch.
    Member : Set
    Member = Fin authorsN

    -- There is a partial isomorphism between NodeIds and the
    -- authors participating in this epoch.
    field
      toNodeId  : Member → NodeId
      isMember? : NodeId → Maybe Member

      nodeid-author-id : ∀{α}     → isMember? (toNodeId α) ≡ just α
      author-nodeid-id : ∀{nid α} → isMember? nid ≡ just α
                                  → toNodeId α ≡ nid

      getPubKey : Member → PK

      PK-inj : ∀ {m1 m2} → getPubKey m1 ≡ getPubKey m2 → m1 ≡ m2

  open EpochConfig

  toNodeId-inj : ∀{𝓔}{x y : Member 𝓔} → toNodeId 𝓔 x ≡ toNodeId 𝓔 y → x ≡ y
  toNodeId-inj {𝓔} hyp = just-injective (trans (sym (nodeid-author-id 𝓔))
                                        (trans (cong (isMember? 𝓔) hyp)
                                               (nodeid-author-id 𝓔)))

  record EpochConfigFor (eid : ℕ) : Set where
    field
     epochConfig : EpochConfig
     forEpochId  : epochId epochConfig ≡ eid

  MemberSubst : ∀ {𝓔} {𝓔'}
              → 𝓔' ≡ 𝓔
              → EpochConfig.Member 𝓔
              → EpochConfig.Member 𝓔'
  MemberSubst refl = id

  -- A member of an epoch is considered "honest" iff its public key is honest.
  Meta-Honest-Member : (𝓔 : EpochConfig) → Member 𝓔 → Set
  Meta-Honest-Member 𝓔 α = Meta-Honest-PK (getPubKey 𝓔 α)

  -- Naturally, if two witnesses that two authors belong
  -- in the epoch are the same, then the authors are also the same.
  --
  -- This proof is very Galois-like, because of the way we structured
  -- our partial isos. It's actually pretty nice! :)
  member≡⇒author≡ : ∀{α β}{𝓔 : EpochConfig}
                  → (authorα : Is-just (isMember? 𝓔 α))
                  → (authorβ : Is-just (isMember? 𝓔 β))
                  → to-witness authorα ≡ to-witness authorβ
                  → α ≡ β
  member≡⇒author≡ {α} {β} {𝓔} a b prf
    with isMember? 𝓔 α | inspect (isMember? 𝓔) α
  ...| nothing | [ _ ] = ⊥-elim (maybe-any-⊥ a)
  member≡⇒author≡ {α} {β} {𝓔} (just _) b prf
     | just ra | [ RA ]
    with isMember? 𝓔 β | inspect (isMember? 𝓔) β
  ...| nothing | [ _ ] = ⊥-elim (maybe-any-⊥ b)
  member≡⇒author≡ {α} {β} {𝓔} (just _) (just _) prf
     | just ra | [ RA ]
     | just rb | [ RB ]
     = trans (sym (author-nodeid-id 𝓔 RA))
             (trans (cong (toNodeId 𝓔) prf)
                    (author-nodeid-id 𝓔 RB))

  -- ValidEpoch specifies a requirement for an epoch to have "enough"
  -- honest verifiers to ensure that any pair of quorums has an honest
  -- peer in its intersection. EpochConfig carries the information that
  -- a peer will have immediately in its state. ValidEpoch, on the
  -- other hand, carries information that the protocol and epoch
  -- changes will need to guarantee.
  record ValidEpoch (𝓔 : EpochConfig) : Set₁ where
    field
      bft-lemma : {xs ys : List (Member 𝓔)}
                -- enforcing both xs and ys to be sorted lists according to
                -- a anti-reflexive linear order ensures authors are distinct.
                → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                → QSize 𝓔 ≤ length xs
                → QSize 𝓔 ≤ length ys
                → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-Member 𝓔 α)

  -- The abstract model is connected to the implementaton by means of
  -- 'VoteEvidence'. The record module will be parameterized by a
  -- v of type 'VoteEvidence 𝓔 UID'; this v will provide evidence
  -- that a given author voted for a given block (identified by the UID)
  -- on the specified round.
  --
  -- When it comes time to instantiate the v above concretely, it will
  -- be something that states that we have a signature from the specified
  -- author voting for the specified block.
  record AbsVoteData (𝓔 : EpochConfig)(UID : Set) : Set where
    constructor mkAbsVoteData
    field
      abs-vRound     : Round
      abs-vMember    : EpochConfig.Member 𝓔
      abs-vBlockUID  : UID
  open AbsVoteData public

  AbsVoteData-η : ∀ {𝓔} {UID : Set} {r1 r2 : Round} {m1 m2 : EpochConfig.Member 𝓔} {b1 b2 : UID}
                → r1 ≡ r2
                → m1 ≡ m2
                → b1 ≡ b2
                → mkAbsVoteData {𝓔} {UID} r1 m1 b1 ≡ mkAbsVoteData r2 m2 b2
  AbsVoteData-η refl refl refl = refl

  VoteEvidence : EpochConfig → Set → Set₁
  VoteEvidence 𝓔 UID = AbsVoteData 𝓔 UID → Set
