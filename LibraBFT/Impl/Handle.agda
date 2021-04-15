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
 open import LibraBFT.Impl.Consensus.ChainedBFT.RoundManager hash hash-cr
 open RWST-do

 -- This represents an uninitialised RoundManager, about which we know nothing, which we use as
 -- the initial RoundManager for every peer until it is initialised.
 postulate
   fakeRM : RoundManager

 -- Eventually, the initialization should establish some properties we care about, but for now we
 -- just initialise again to fakeRM, which means we cannot prove the base case for various
 -- properties, e.g., in Impl.Properties.VotesOnce
 initialRoundManagerAndMessages
     : (a : Author) → EpochConfig → RoundManager
     → RoundManager × List NetworkMsg
 initialRoundManagerAndMessages a _ _ = fakeRM , []

 handle : NodeId → NetworkMsg → Instant → LBFT Unit
 handle _self msg now
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
 outputToActions : RoundManager → Output → List (Action NetworkMsg)
 outputToActions rm (BroadcastProposal p) = List-map (const (Action.send (P p)))
                                                     (List-map proj₁
                                                               (kvm-toList (:vvAddressToValidatorInfo (₋rmValidators (₋rmEC rm)))))
 outputToActions _  (LogErr x)            = []
 outputToActions _  (SendVote v toList)   = List-map (const (Action.send (V v))) toList

 outputsToActions : ∀ {State} → List Output → List (Action NetworkMsg)
 outputsToActions {st} = concat ∘ List-map (outputToActions st)

 runHandler : RoundManager → LBFT Unit → RoundManager × List (Action NetworkMsg)
 runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

 -- And ultimately, the all-knowing system layer only cares about the
 -- step function.
 peerStep : NodeId → NetworkMsg → Instant → RoundManager → RoundManager × List (Action NetworkMsg)
 peerStep nid msg ts st = runHandler st (handle nid msg ts)

 -- This (temporary) wrapper bridges the gap between our (draft) concrete handler and
 -- the form required by the new system model, which does not (yet) support actions other
 -- than send.
 peerStepWrapper : NodeId → NetworkMsg → RoundManager → RoundManager × List NetworkMsg
 peerStepWrapper nid msg st = ×-map₂ (List-map msgToSend) (peerStep nid msg 0 st)
