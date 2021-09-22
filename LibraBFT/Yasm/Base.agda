{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Types

-- This module defines the types used to define a SystemModel.
module LibraBFT.Yasm.Base (ℓ-PeerState : Level) where
 -- Our system is configured through a value of type
 -- SystemParameters where we specify:
 record SystemTypeParameters : Set (ℓ+1 ℓ-PeerState) where
  constructor mkSysTypeParms
  field
    PeerId    : Set
    _≟PeerId_ : ∀ (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
    Genesis   : Set
    -- A relation specifying what Signatures are included in genInfo
    ∈GenInfo  : Genesis → Signature → Set
    PeerState : Set ℓ-PeerState
    Msg       : Set
    Part      : Set -- Types of interest that can be represented in Msgs

    -- The messages must be able to carry signatures
    instance Part-sig : WithSig Part

    -- A relation specifying what Parts are included in a Msg.

    -- TODO-2: I changed the name of this to append the G because of the pain disambiguating it from
    -- NetworkMsg.⊂Msg.  This issue https://github.com/agda/agda/issues/2175 suggests I should have
    -- been able to get this right without renaming, but...  I'd like to underastand how to do this
    -- right, but for expedience, not now.
    _⊂MsgG_       : Part → Msg → Set

 module _ (systypes : SystemTypeParameters) where
   open SystemTypeParameters systypes

   record SystemInitAndHandlers : Set (ℓ+1 ℓ-PeerState) where
    constructor mkSysInitAndHandlers
    field
      -- The same genesis information is given to any uninitialised peer before
      -- it can handle any messages.
      genInfo   : Genesis

      -- Represents an uninitialised PeerState, about which we know nothing whatsoever
      initPS    : PeerState

      -- Bootstraps a peer.
      -- TODO-1 : replace Maybe with Either after adding error type (to mkSysTypeParms ?).
      bootstrap : PeerId → Genesis → Maybe (PeerState × List (Action Msg))

      -- Handles a message on a previously initialized peer.
      -- TODO-1 : replace Maybe with Either after adding error type (to mkSysTypeParms ?).
      handle : PeerId → Msg → PeerState → Maybe (PeerState × List (Action Msg))

