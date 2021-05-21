{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

-- This module defines types used in the specification of a SystemModel.
module LibraBFT.Yasm.Types where

-- Actions that can be performed by peers.
-- For now, the SystemModel supports only one kind of action: to send a
-- message. Later it might include things like logging, crashes, assertion
-- failures, etc.
data Action (Msg : Set) : Set where
  send : (m : Msg) → Action Msg

-- Injectivity of `send`.
action-send-injective : ∀ {Msg}{m m' : Msg} → send m ≡ send m' → m ≡ m'
action-send-injective refl = refl
