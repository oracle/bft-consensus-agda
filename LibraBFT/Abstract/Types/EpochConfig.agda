{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
-- TODO-2: The following import should be eliminated and replaced
-- with the necessary module parameters (PK and MetaHonestPK)
open import LibraBFT.Base.PKCS

-- This module brings in the base types used through libra
-- and those necessary for the abstract model.
module LibraBFT.Abstract.Types.EpochConfig
  (UID    : Set)
  (NodeId : Set)
  where

  open import LibraBFT.Base.Types

  -- An epoch-configuration carries only simple data about the epoch; the complicated
  -- parts will be provided by the System, defined below.
  --
  -- The reason for the separation is that we should be able to provide
  -- an EpochConfig from a single peer state.
  record EpochConfig : Set₁ where
    constructor EpochConfig∙new
    field
      genesisUID : UID
      epoch      : Epoch
      authorsN  : ℕ

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

      IsQuorum : List Member → Set

      bft-assumption : ∀ {xs ys}
                     → IsQuorum xs → IsQuorum ys
                     → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-PK (getPubKey α))

  open EpochConfig

  module _ (ec : EpochConfig) where
    NodeId-PK-OK : PK → NodeId → Set
    NodeId-PK-OK pk pid = ∃[ m ] (toNodeId ec m ≡ pid × getPubKey ec m ≡ pk)

    NodeId-PK-OK-injective : ∀ {pk pid1 pid2}
                           → NodeId-PK-OK pk pid1
                           → NodeId-PK-OK pk pid2
                           → pid1 ≡ pid2
    NodeId-PK-OK-injective (m1 , pid1 , pk1) (m2 , pid2 , pk2)
       rewrite PK-inj ec (trans pk1 (sym pk2)) = trans (sym pid1) pid2

  module WithAbsVote (𝓔 : EpochConfig) where
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
      constructor AbsVoteData∙new
      field
        abs-vRound     : Round
        abs-vMember    : EpochConfig.Member 𝓔
        abs-vBlockUID  : UID
    open AbsVoteData public

    AbsVoteData-η : ∀ {r1 r2 : Round} {m1 m2 : EpochConfig.Member 𝓔} {b1 b2 : UID}
                  → r1 ≡ r2
                  → m1 ≡ m2
                  → b1 ≡ b2
                  → AbsVoteData∙new r1 m1 b1 ≡ AbsVoteData∙new r2 m2 b2
    AbsVoteData-η refl refl refl = refl

    VoteEvidence : Set₁
    VoteEvidence = AbsVoteData → Set
