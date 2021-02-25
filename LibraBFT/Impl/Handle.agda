{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

-- This module provides some scaffolding to define the handlers for our fake/simple
-- "implementation" and connect them to the interface of the SystemModel.

module LibraBFT.Impl.Handle
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
 open import LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor hash hash-cr
 open RWST-do

 postulate
   fakeEP : EventProcessor

 initialEventProcessorAndMessages
     : (a : Author) → EpochConfig → Maybe EventProcessor
     → EventProcessor × List NetworkMsg
 initialEventProcessorAndMessages a _ mep = fakeEP , []

 handle : NodeId × NetworkMsg → Instant → LBFT Unit
 handle (sender , msg) now
    with msg
 ...| P p = processProposalMsg now p
 ...| V v = processVote now v
 ...| C c = return unit            -- We don't do anything with commit messages, they are just for defining Correctness.

 -- For now, the SystemModel supports only one kind of action: to send a Message.  Later it might
 -- include things like logging, crashes, assertion failures, etc.  At that point, definitions like
 -- the following might become part of the SystemModel, but they are included here to enable the
 -- temporary scaffolding below.

 data Action (Msg : Set) : Set where
   send : Msg → Action Msg

 action-send-injective : ∀ {Msg}{m m' : Msg} → send m ≡ send m' → m ≡ m'
 action-send-injective refl = refl

 msgToSend : {Msg : Set} → Action Msg → Msg
 msgToSend (send m) = m

 msgToSend≡ : ∀ {Msg x}{m : Msg} → m ≡ msgToSend x → send m ≡ x
 msgToSend≡ {_} {send m} {m} refl = refl

 -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
 -- it is included in the model only to facilitate future work on liveness properties, when we will need
 -- assumptions about message delivery between honest peers.
 outputToActions : EventProcessor → Output → List (Action NetworkMsg)
 outputToActions ep (BroadcastProposal p) = List-map (const (Action.send (P p)))
                                                     (List-map proj₁
                                                               (kvm-toList (:vvAddressToValidatorInfo (₋epValidators (₋epEC ep)))))
 outputToActions _  (LogErr x)            = []
 outputToActions _  (SendVote v toList)   = List-map (const (Action.send (V v))) toList

 outputsToActions : ∀ {State} → List Output → List (Action NetworkMsg)
 outputsToActions {st} = concat ∘ List-map (outputToActions st)

 runHandler : EventProcessor → LBFT Unit → EventProcessor × List (Action NetworkMsg)
 runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (RWST-run handler unit st))

 -- And ultimately, the all-knowing system layer only cares about the
 -- step function.
 peerStep : NodeId × NetworkMsg → Instant → EventProcessor → EventProcessor × List (Action NetworkMsg)
 peerStep msg ts st = runHandler st (handle msg ts)

 -- This (temporary) wrapper bridges the gap between our (draft) concrete handler and
 -- the form required by the new system model, which does not (yet) support actions other
 -- than send.
 peerStepWrapper : NodeId → NetworkMsg → EventProcessor → EventProcessor × List NetworkMsg
 peerStepWrapper id msg st
    -- run the handler
    with peerStep (id , msg) 0 st
 ...| st' , acts
    -- extract the messages to be sent
    with List-map msgToSend acts
    -- send them and record that they were sent in the peer state
 ...| msgs = record st' {₋epMeta-Msgs = ₋epMeta-Msgs st' ++ msgs } , msgs
