{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

-- This module defines types used in the specification of a SystemModel.
module LibraBFT.Yasm.Types where

-- Actions that can be performed by peers.
--
-- For now, the SystemModel supports only one kind of action: to send a
-- message. Later it might include things like logging, crashes, assertion
-- failures, etc. For example, if an assertion fires, this
-- could "kill the process" and make it not send any messages in the future.
-- We could also then prove that the handlers do not crash, certain
-- messages are logged under certain circumstances, etc.
--
-- Alternatively, certain actions can be kept outside the system model by
-- defining an application-specific PeerState type (see `LibraBFT.Yasm.Base`).
-- For example:
--
-- > libraHandle : Msg → Status × Log × LState → Status × LState × List Action
-- > libraHandle _ (Crashed , l , s) = Crashed , s , [] -- i.e., crashed peers never send messages
-- >
-- > handle = filter isSend ∘ libraHandle
data Action (Msg : Set) : Set where
  send : (m : Msg) → Action Msg

-- Injectivity of `send`.
action-send-injective : ∀ {Msg}{m m' : Msg} → send m ≡ send m' → m ≡ m'
action-send-injective refl = refl
