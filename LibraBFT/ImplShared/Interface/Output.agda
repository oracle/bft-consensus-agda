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
open import Optics.All

module LibraBFT.ImplShared.Interface.Output where

  data Output : Set where
    BroadcastProposal : ProposalMsg → List Author     → Output
    BroadcastSyncInfo : SyncInfo    → List Author     → Output
    LogErr            : ErrLog                        → Output
    LogInfo           : InfoLog                       → Output
    SendVote          : VoteMsg → List Author → Output
  open Output public

  SendVote-inj-v : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → x1 ≡ x2
  SendVote-inj-v refl = refl

  SendVote-inj-si : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → y1 ≡ y2
  SendVote-inj-si refl = refl

  IsSendVote : Output → Set
  IsSendVote (BroadcastProposal _ _) = ⊥
  IsSendVote (BroadcastSyncInfo _ _) = ⊥
  IsSendVote (LogErr _) = ⊥
  IsSendVote (LogInfo _) = ⊥
  IsSendVote (SendVote _ _) = ⊤

  IsBroadcastProposal : Output → Set
  IsBroadcastProposal (BroadcastProposal _ _) = ⊤
  IsBroadcastProposal (BroadcastSyncInfo _ _) = ⊥
  IsBroadcastProposal (LogErr _) = ⊥
  IsBroadcastProposal (LogInfo _) = ⊥
  IsBroadcastProposal (SendVote _ _) = ⊥

  IsBroadcastSyncInfo : Output → Set
  IsBroadcastSyncInfo (BroadcastProposal _ _) = ⊥
  IsBroadcastSyncInfo (BroadcastSyncInfo _ _) = ⊤
  IsBroadcastSyncInfo (LogErr _)              = ⊥
  IsBroadcastSyncInfo (LogInfo _)             = ⊥
  IsBroadcastSyncInfo (SendVote _ _)          = ⊥

  IsLogErr : Output → Set
  IsLogErr (BroadcastProposal _ _) = ⊥
  IsLogErr (BroadcastSyncInfo _ _) = ⊥
  IsLogErr (LogErr _)            = ⊤
  IsLogErr (LogInfo _)           = ⊥
  IsLogErr (SendVote _ _)        = ⊥

  isSendVote? : (out : Output) → Dec (IsSendVote out)
  isSendVote? (BroadcastProposal _ _) = no λ ()
  isSendVote? (BroadcastSyncInfo _ _) = no λ ()
  isSendVote? (LogErr _)            = no λ ()
  isSendVote? (LogInfo _)           = no λ ()
  isSendVote? (SendVote mv pid)     = yes tt

  isBroadcastProposal? : (out : Output) →  Dec (IsBroadcastProposal out)
  isBroadcastProposal? (BroadcastProposal _ _) = yes tt
  isBroadcastProposal? (BroadcastSyncInfo _ _) = no λ ()
  isBroadcastProposal? (LogErr _)            = no λ ()
  isBroadcastProposal? (LogInfo _)           = no λ ()
  isBroadcastProposal? (SendVote _ _)        = no λ ()

  isBroadcastSyncInfo? : (out : Output) →  Dec (IsBroadcastSyncInfo out)
  isBroadcastSyncInfo? (BroadcastProposal _ _) = no λ ()
  isBroadcastSyncInfo? (BroadcastSyncInfo _ _) = yes tt
  isBroadcastSyncInfo? (LogErr _)              = no λ ()
  isBroadcastSyncInfo? (LogInfo _)             = no λ ()
  isBroadcastSyncInfo? (SendVote _ _)          = no λ ()

  isLogErr? : (out : Output) → Dec (IsLogErr out)
  isLogErr? (BroadcastProposal x _) = no λ ()
  isLogErr? (BroadcastSyncInfo x _) = no λ ()
  isLogErr? (LogErr x)            = yes tt
  isLogErr? (LogInfo x)           = no λ ()
  isLogErr? (SendVote x x₁)       = no λ ()

  IsOutputMsg : Output → Set
  IsOutputMsg = IsBroadcastProposal ∪ IsBroadcastSyncInfo ∪ IsSendVote

  isOutputMsg? = (isBroadcastProposal? ∪? isBroadcastSyncInfo?) ∪? isSendVote?

  data _Msg∈Out_ : NetworkMsg → Output → Set where
    inBP : ∀ {pm pids} → P pm Msg∈Out BroadcastProposal pm pids
    inSV : ∀ {vm pids} → V vm Msg∈Out SendVote vm pids

  sendVote∉Output : ∀ {vm pid outs} → List-filter isSendVote? outs ≡ [] → ¬ (SendVote vm pid ∈ outs)
  sendVote∉Output () (here refl)
  sendVote∉Output{outs = x ∷ outs'} eq (there vm∈outs)
     with isSendVote? x
  ... | no proof = sendVote∉Output eq vm∈outs

  -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
  -- it is included in the model only to facilitate future work on liveness properties, when we will need
  -- assumptions about message delivery between honest peers.
  outputToActions : RoundManager → Output → List (Action NetworkMsg)
  outputToActions rm (BroadcastProposal p rcvrs) = List-map (const (send (P p))) rcvrs
  outputToActions _  (BroadcastSyncInfo _ _) = []
  outputToActions _  (LogErr x)            = []
  outputToActions _  (LogInfo x)           = []
  outputToActions _  (SendVote vm rcvrs)   = List-map (const (send (V vm))) rcvrs

  outputsToActions : ∀ {State} → List Output → List (Action NetworkMsg)
  outputsToActions {st} = concat ∘ List-map (outputToActions st)

  -- Lemmas about `outputsToActions`
  outputToActions-sendVote∉actions
    : ∀ {out vm st} → ¬ (IsSendVote out) → ¬ (send (V vm) ∈ outputToActions st out)
  outputToActions-sendVote∉actions {BroadcastProposal pm rcvrs}{vm}{st} ¬sv m∈acts =
    help rcvrs m∈acts
    where
    help : ∀ xs → ¬ (send (V vm) ∈ List-map (const (send (P pm))) xs)
    help (x ∷ xs) (there m∈acts) = help xs m∈acts
  outputToActions-sendVote∉actions {SendVote _ _} ¬sv m∈acts = ¬sv tt

  outputToActions-m∈sendVoteList
    : ∀ {m vm rcvrs} → send m ∈ List-map (const $ send (V vm)) rcvrs
      → m Msg∈Out SendVote vm rcvrs
  outputToActions-m∈sendVoteList {.(V vm)} {vm} {x ∷ rcvrs} (here refl) = inSV
  outputToActions-m∈sendVoteList {m} {vm} {x ∷ rcvrs} (there m∈svl)
    with outputToActions-m∈sendVoteList{rcvrs = rcvrs} m∈svl
  ... | inSV = inSV

  outputToActions-m∈sendProposalList
    : ∀ {m pm rcvrs} → send m ∈ List-map (const $ send (P pm)) rcvrs
      → m Msg∈Out BroadcastProposal pm rcvrs
  outputToActions-m∈sendProposalList {.(P pm)} {pm} {x ∷ rcvrs} (here refl) = inBP
  outputToActions-m∈sendProposalList {m} {pm} {x ∷ rcvrs} (there m∈spl)
    with outputToActions-m∈sendProposalList {rcvrs = rcvrs} m∈spl
  ... | inBP = inBP

  sendVote∉actions
    : ∀ {outs vm st} → [] ≡ List-filter isSendVote? outs → ¬ (send (V vm) ∈ outputsToActions{st} outs)
  sendVote∉actions {[]} {st = st} outs≡ ()
  sendVote∉actions {x ∷ outs} {st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st x) m∈acts
  ... | Left m∈[]
    with isSendVote? x
  ...| no  proof = outputToActions-sendVote∉actions {st = st} proof m∈[]
  sendVote∉actions {x ∷ outs} {st = st} outs≡ m∈acts | Right m∈acts'
    with isSendVote? x
  ...| no  proof = sendVote∉actions{outs = outs}{st = st} outs≡ m∈acts'

  sendVote∈actions
    : ∀ {vm vm' pids outs st} → SendVote vm pids ∷ [] ≡ List-filter isSendVote? outs
      → send (V vm') ∈ outputsToActions{st} outs
      → vm' ≡ vm
  sendVote∈actions {outs = (BroadcastProposal x rcvrs) ∷ outs}{st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st (BroadcastProposal x rcvrs)) m∈acts
  ... | Left m∈[] = ⊥-elim (outputToActions-sendVote∉actions{out = BroadcastProposal x rcvrs}{st = st} id m∈[])
  ... | Right m∈acts' = sendVote∈actions{outs = outs}{st = st} outs≡ m∈acts'
  sendVote∈actions {outs = (BroadcastSyncInfo x rcvrs) ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions{outs = outs}{st = st} outs≡ m∈acts
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

  sendMsg∈actions
    : ∀ {outs m st} → send m ∈ outputsToActions{st} outs
      → Σ[ out ∈ Output ] (out ∈ outs × m Msg∈Out out)
  sendMsg∈actions {BroadcastProposal pm rcvrs ∷ outs} {m} {st} m∈acts
    with Any-++⁻ (List-map (const $ send (P pm)) rcvrs) m∈acts
  ... | Left m∈bpl =
    BroadcastProposal pm rcvrs , here refl , outputToActions-m∈sendProposalList m∈bpl
  ... | Right m∈acts'
    with sendMsg∈actions{outs}{m}{st} m∈acts'
  ... | out , out∈outs , m∈out = out , there out∈outs , m∈out
  -- NOTE: When we represent sending `BroadcastSyncInfo` as an action, this will require updating
  sendMsg∈actions {BroadcastSyncInfo _ _ ∷ outs} {m} {st} m∈acts
    with sendMsg∈actions{outs}{m}{st} m∈acts
  ...| out , out∈outs , m∈out = out , there out∈outs , m∈out
  sendMsg∈actions {LogErr _ ∷ outs} {m} {st} m∈acts
    with sendMsg∈actions{outs}{m}{st} m∈acts
  ...| out , out∈outs , m∈out = out , there out∈outs , m∈out
  sendMsg∈actions {LogInfo _ ∷ outs} {m} {st} m∈acts
    with sendMsg∈actions{outs}{m}{st} m∈acts
  ...| out , out∈outs , m∈out = out , there out∈outs , m∈out
  sendMsg∈actions {SendVote vm rcvrs ∷ outs} {m} {st} m∈acts
    with Any-++⁻ (List-map (const (send (V vm))) rcvrs) m∈acts
  ... | Left m∈svl =
    SendVote vm rcvrs , here refl , outputToActions-m∈sendVoteList m∈svl
  ... | Right m∈acts'
    with sendMsg∈actions{outs}{m}{st} m∈acts'
  ... | out , out∈outs , m∈out = out , there out∈outs , m∈out
