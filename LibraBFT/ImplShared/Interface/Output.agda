{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module defines Outputs produced by handlers, as well as functions and properties relating
-- these to Yasm Actions.

open import LibraBFT.Base.KVMap
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Types

module LibraBFT.ImplShared.Interface.Output where

  data Output : Set where
    BroadcastProposal : ProposalMsg                   → Output
    LogErr            : ErrLog                        → Output
    LogInfo           : InfoLog                       → Output
    SendVote          : VoteMsg → List Author → Output
  open Output public

  SendVote-inj-v : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → x1 ≡ x2
  SendVote-inj-v refl = refl

  SendVote-inj-si : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → y1 ≡ y2
  SendVote-inj-si refl = refl

  IsSendVote : Output → Set
  IsSendVote (BroadcastProposal _) = ⊥
  IsSendVote (LogErr _) = ⊥
  IsSendVote (LogInfo _) = ⊥
  IsSendVote (SendVote _ _) = ⊤

  IsBroadcastProposal : Output → Set
  IsBroadcastProposal (BroadcastProposal _) = ⊤
  IsBroadcastProposal (LogErr _) = ⊥
  IsBroadcastProposal (LogInfo _) = ⊥
  IsBroadcastProposal (SendVote _ _) = ⊥

  IsLogErr : Output → Set
  IsLogErr (BroadcastProposal _) = ⊥
  IsLogErr (LogErr _)            = ⊤
  IsLogErr (LogInfo _)           = ⊥
  IsLogErr (SendVote _ _)        = ⊥

  isSendVote? : (out : Output) → Dec (IsSendVote out)
  isSendVote? (BroadcastProposal _) = no λ ()
  isSendVote? (LogErr _)            = no λ ()
  isSendVote? (LogInfo _)           = no λ ()
  isSendVote? (SendVote mv pid)     = yes tt

  isBroadcastProposal? : (out : Output) →  Dec (IsBroadcastProposal out)
  isBroadcastProposal? (BroadcastProposal _) = yes tt
  isBroadcastProposal? (LogErr _)            = no λ ()
  isBroadcastProposal? (LogInfo _)           = no λ ()
  isBroadcastProposal? (SendVote _ _)        = no λ ()

  isLogErr? : (out : Output) → Dec (IsLogErr out)
  isLogErr? (BroadcastProposal x) = no λ ()
  isLogErr? (LogErr x)            = yes tt
  isLogErr? (LogInfo x)           = no λ ()
  isLogErr? (SendVote x x₁)       = no λ ()

  IsOutputMsg : Output → Set
  IsOutputMsg = IsBroadcastProposal ∪ IsSendVote

  isOutputMsg? = isBroadcastProposal? ∪? isSendVote?

  SendVote∉Output : ∀ {vm pid outs} → List-filter isSendVote? outs ≡ [] → ¬ (SendVote vm pid ∈ outs)
  SendVote∉Output () (here refl)
  SendVote∉Output{outs = x ∷ outs'} eq (there vm∈outs)
     with isSendVote? x
  ... | no proof = SendVote∉Output eq vm∈outs

  -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
  -- it is included in the model only to facilitate future work on liveness properties, when we will need
  -- assumptions about message delivery between honest peers.
  outputToActions : RoundManager → Output → List (Action NetworkMsg)
  outputToActions rm (BroadcastProposal p) = List-map (const (send (P p)))
                                                      (List-map proj₁
                                                                (kvm-toList (_vvAddressToValidatorInfo
                                                                              (_esVerifier
                                                                                (_rmEpochState (_rmEC rm))))))
  outputToActions _  (LogErr x)            = []
  outputToActions _  (LogInfo x)           = []
  outputToActions _  (SendVote vm toList)  = List-map (const (send (V vm))) toList

  outputsToActions : ∀ {State} → List Output → List (Action NetworkMsg)
  outputsToActions {st} = concat ∘ List-map (outputToActions st)

  -- Lemmas about `outputsToActions`
  outputToActions-sendVote∉actions
    : ∀ {out vm st} → ¬ (IsSendVote out) → ¬ (send (V vm) ∈ outputToActions st out)
  outputToActions-sendVote∉actions {BroadcastProposal pm}{vm}{st} ¬sv m∈acts =
    help (kvm-toList (_vvAddressToValidatorInfo (_esVerifier (_rmEpochState (_rmEC st))))) m∈acts
    where
    help : ∀ xs → ¬ (send (V vm) ∈ List-map (const (send (P pm))) (List-map proj₁ xs))
    help (x ∷ xs) (there m∈acts) = help xs m∈acts
  outputToActions-sendVote∉actions {SendVote _ _} ¬sv m∈acts = ¬sv tt

  sendVote∉actions
    : ∀ {outs vm st} → [] ≡ List-filter isSendVote? outs → ¬ (send (V vm) ∈ outputsToActions{st} outs)
  sendVote∉actions {[]} {st = st} outs≡ ()
  sendVote∉actions {x ∷ outs} {st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st x) m∈acts
  ... | Left m∈[]
    with isSendVote? x
  ...| no  proof = outputToActions-sendVote∉actions proof m∈[]
  sendVote∉actions {x ∷ outs} {st = st} outs≡ m∈acts | Right m∈acts'
    with isSendVote? x
  ...| no  proof = sendVote∉actions{outs = outs}{st = st} outs≡ m∈acts'

  sendVote∈actions
    : ∀ {vm vm' pids outs st} → SendVote vm pids ∷ [] ≡ List-filter isSendVote? outs
      → send (V vm') ∈ outputsToActions{st} outs
      → vm' ≡ vm
  sendVote∈actions {outs = BroadcastProposal x ∷ outs}{st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st (BroadcastProposal x)) m∈acts
  ... | Left m∈[] = ⊥-elim (outputToActions-sendVote∉actions{out = BroadcastProposal x}{st = st} id m∈[])
  ... | Right m∈acts' = sendVote∈actions{outs = outs}{st = st} outs≡ m∈acts'
  sendVote∈actions {outs = LogErr x ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions{outs = outs}{st = st} outs≡ m∈acts
  sendVote∈actions {outs = LogInfo x ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions{outs = outs}{st = st} outs≡ m∈acts
  sendVote∈actions {vm}{vm'}{outs = SendVote vm“ pids' ∷ outs}{st = st} outs≡ m∈acts
    with ∷-injective outs≡
  ...| refl , tl≡
    with Any-++⁻ (List-map (const (send (V vm“))) pids') m∈acts
  ... | Right m∈[] = ⊥-elim (sendVote∉actions{outs = outs}{st = st} tl≡ m∈[])
  ... | Left m∈acts' = help pids' m∈acts'
    where
    help : ∀ pids → send (V vm') ∈ List-map (const (send (V vm“))) pids → vm' ≡ vm“
    help (_ ∷ pids) (here refl) = refl
    help (_ ∷ pids) (there m∈acts) = help pids m∈acts

  -- sendVote∈actions {pids = _} {SendVote vm' [] ∷ outs} outs≡ m∈acts | refl , outsTl≡ = ⊥-elim (sendVote∉actions{outs} outsTl≡ m∈acts)
  -- sendVote∈actions {pids = _} {SendVote vm' (x ∷ pids') ∷ outs} outs≡ (here px) | refl , outsTl≡ = {!!}
  -- sendVote∈actions {pids = _} {SendVote vm' (x ∷ pids') ∷ outs} outs≡ (there m∈acts) | refl , outsTl≡ = {!!}
