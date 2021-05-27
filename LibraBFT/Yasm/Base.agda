{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

open import LibraBFT.Yasm.Types

-- This module defines the types used to define a SystemModel.
module LibraBFT.Yasm.Base (ℓ-PeerState : Level) where
 -- Our system is configured through a value of type
 -- SystemParameters where we specify:
 record SystemParameters : Set (ℓ+1 ℓ-PeerState) where
  constructor mkSysParms
  field
    PeerId    : Set
    _≟PeerId_ : ∀ (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
    Genesis   : Set
    genInfo   : Genesis    -- The same genesis information is given to any uninitialised peer before
                           -- it can handle any messages.
    PeerState : Set ℓ-PeerState
    initPS    : PeerState  -- Represents an uninitialised PeerState, about which we know nothing whatsoever
    Msg       : Set
    Part      : Set -- Types of interest that can be represented in Msgs

    -- The messages must be able to carry signatures
    instance Part-sig : WithSig Part

    -- A relation specifying what Parts are included in a Msg.
    _⊂Msg_       : Part → Msg → Set

    -- A relation specifying what Signatures are included in genInfo
    ∈GenInfo     : Signature → Set

    -- Initializes a potentially-empty state with an EpochConfig
    init : PeerId → Genesis → PeerState × List (Action Msg)

    -- Handles a message on a previously initialized peer.
    handle : PeerId → Msg → PeerState → PeerState × List (Action Msg)

