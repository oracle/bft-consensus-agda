{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
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
    constructor mkEpochConfig
    field
      genesisUID : UID
      epochId   : EpochId
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

  record EpochConfigFor (eid : ℕ) : Set₁ where
    field
     epochConfig : EpochConfig
     forEpochId  : epochId epochConfig ≡ eid
