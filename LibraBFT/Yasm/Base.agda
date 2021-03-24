{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

-- This module defines the types used to define a SystemModel.

module LibraBFT.Yasm.Base
  (ℓ-EC        : Level)
  (EpochConfig : Set ℓ-EC)
  (epochId     : EpochConfig → ℕ)
  (authorsN    : EpochConfig → ℕ)
 where

 EpochId : Set
 EpochId = ℕ

 Member : EpochConfig → Set
 Member = Fin ∘ authorsN

 record EpochConfigFor (eid : EpochId) : Set ℓ-EC where
   field
    epochConfig : EpochConfig
    forEpochId  : epochId epochConfig ≡ eid

 -- Our system is configured through a value of type
 -- SystemParameters where we specify:
 record SystemParameters : Set ((ℓ+1 0ℓ) ℓ⊔ ℓ-EC) where
  constructor mkSysParms
  field
    PeerId    : Set
    PeerState : Set
    Msg       : Set
    Part      : Set -- Types of interest that can be represented in Msgs

    -- The messages must be able to carry signatures
    instance Part-sig : WithSig Part

    -- A relation specifying what Parts are included in a Msg.
    _⊂Msg_       : Part → Msg → Set

    -- Finally, messages must carry an epoch id and might have an author
    part-epoch  : Part → EpochId

    -- A decidable over PeerId's
    _≟Peer_ : ∀ (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)

    -- Initializes a potentially-empty state with an EpochConfig
    init : PeerId → EpochConfig → Maybe PeerState → PeerState × List Msg

    -- Handles a message on a previously initialized peer.
    handle : PeerId → Msg → PeerState → PeerState × List Msg

    -- TODO-3?: So far, handlers only produce messages to be sent.
    -- It would be reasonable to generalize this to something like
    --
    --   data Action = Send Msg | Crash CrashMsg | Log LogMsg | ...
    --
    -- on the system level, and have the handlers return List Action,
    -- rather than just ListMsg.  For example, if an assertion fires, this
    -- could "kill the process" and make it not send any messages in the future.
    -- We could also then prove that the handlers do not crash, certain
    -- messages are logged under certain circumstances, etc.
    --
    -- Alternatively, we could keep this outside the system model by
    -- defining an application-specific peerState type, for example:
    --
    -- > libraHandle : Msg → Status × Log × LState → Status × LState × List Action
    -- > libraHandle _ (Crashed , l , s) = Crashed , s , [] -- i.e., crashed peers never send messages
    -- >
    -- > handle = filter isSend ∘ libraHandle

 -- We also require a standard key-value store interface, along with its
 -- functionality and various properties about it.  Most of the properties
 -- are not currently used, but they are included here based on our
 -- experience in other work, as we think many of them will be needed when
 -- reasoning about an actual LibraBFT implementation.

 -- Although we believe the assumptions here are reasonable, it is always
 -- possible that we made a mistake in postulating one of the properties,
 -- making it impossible to implement.  Thus, it would a useful contribution
 -- to:
 --
 -- TODO-1: construct an actual implementation and provide and prove the
 -- necessary properties to satisfy the requirements of this module
 --
 -- Note that this would require some work, but should be relatively
 -- straightforward and requires only "local" changes.

 postulate
   Map        : Set → Set → Set
   Map-empty  : ∀{k v} → Map k v
   Map-lookup : ∀{k v} → k → Map k v → Maybe v
   Map-insert : ∀{k v} → k → v → Map k v → Map k v
   Map-set    : ∀{k v} → k → Maybe v → Map k v → Map k v

   -- It must satisfy the following properties
   Map-insert-correct  : ∀ {K V : Set}{k : K}{v : V}{m : Map K V}
                       → Map-lookup k (Map-insert k v m) ≡ just v

   Map-insert-target-≢ : ∀ {K V : Set}{k k' : K}{v : V}{m}
                       → k' ≢ k
                       → Map-lookup k' m ≡ Map-lookup k' (Map-insert k v m)

   Map-set-correct     : ∀ {K V : Set}{k : K}{mv : Maybe V}{m : Map K V}
                       → Map-lookup k (Map-set k mv m) ≡ mv

   Map-set-target-≢    : ∀ {K V : Set}{k k' : K}{mv : Maybe V}{m}
                       → k' ≢ k
                       → Map-lookup k' m ≡ Map-lookup k' (Map-set k mv m)

   Map-set-≡-correct   : ∀ {K V : Set}{k : K}{m : Map K V}
                       → Map-set k (Map-lookup k m) m ≡ m
