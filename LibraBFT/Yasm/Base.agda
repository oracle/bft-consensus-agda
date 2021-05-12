{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

-- This module defines the types used to define a SystemModel.

module LibraBFT.Yasm.Base (ℓ-PeerState : Level) where

 -- Our system is configured through a value of type
 -- SystemParameters where we specify:
 record SystemParameters : Set (ℓ+1 ℓ-PeerState) where
  constructor mkSysParms
  field
    PeerId    : Set
    _≟PeerId_ : ∀ (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
    PeerState : Set ℓ-PeerState
    Msg       : Set
    Part      : Set -- Types of interest that can be represented in Msgs

    -- The messages must be able to carry signatures
    instance Part-sig : WithSig Part

    -- A relation specifying what Parts are included in a Msg.
    _⊂Msg_       : Part → Msg → Set

    initPS      : PeerState -- Represents an uninitialised PeerState, about which we know nothing whatsoever
    initMsg     : Msg       -- An initial message
    initMsgSndr : PeerId    -- Who sends the initial message?

    -- Initializes a potentially-empty state with an EpochConfig
    initPeer    : PeerId → (PeerId × Msg) → PeerState × List Msg

    -- Handles a message on a previously initialized peer.
    handle      : PeerId → Msg → PeerState → PeerState × List Msg

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

 module _ (parms : SystemParameters) where

   open SystemParameters parms

   -- This type encapsulates properties about parts represented in the inital message
   record InitPartProps : Set₁ where
     constructor mkInitPartProps
     field
       -- A property that should hold for all parts in the initial message...
       InitPartP  : Part → Set
       -- ... and proof that it does
       initPartsP : ∀ {p} → p ⊂Msg initMsg → InitPartP p
       -- If one part satisfies InitMsgP, so does another with the same signature
       initPartSS : SameSig⇒ ⦃ Part-sig ⦄ InitPartP
