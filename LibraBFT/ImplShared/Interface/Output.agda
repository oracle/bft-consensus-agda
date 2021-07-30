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

  -- TODO-2: Eliminate the precendence inconsistency that requires this silly thing
  silly : ∀ {x} → IsOutputMsg x → ((IsBroadcastProposal x ⊎ IsBroadcastSyncInfo x) ⊎ (IsSendVote x))
  silly (Left x)          = Left (Left x)
  silly (Right (Left y))  = Left (Right y)
  silly (Right (Right y)) = Right y

  SendVote∉Output : ∀ {vm pid outs} → List-filter isSendVote? outs ≡ [] → ¬ (SendVote vm pid ∈ outs)
  SendVote∉Output () (here refl)
  SendVote∉Output{outs = x ∷ outs'} eq (there vm∈outs)
     with isSendVote? x
  ... | no proof = SendVote∉Output eq vm∈outs

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
  postulate -- TODO-1: prove it
    outputToActions-sendMsg∉actions
      : ∀ {out m st} → ¬ (IsOutputMsg out) → ¬ (send m ∈ outputToActions st out)

  outputToActions-sendVote∉actions
    : ∀ {out vm st} → ¬ (IsSendVote out) → ¬ (send (V vm) ∈ outputToActions st out)
  outputToActions-sendVote∉actions {BroadcastProposal pm rcvrs}{vm}{st} ¬sv m∈acts =
    help rcvrs m∈acts
    where
    help : ∀ xs → ¬ (send (V vm) ∈ List-map (const (send (P pm))) xs)
    help (x ∷ xs) (there m∈acts) = help xs m∈acts
  outputToActions-sendVote∉actions {SendVote _ _} ¬sv m∈acts = ¬sv tt

  postulate -- TODO-1: prove it
    sendMsg∉actions
      : ∀ {outs m st} → [] ≡ List-filter isOutputMsg? outs → ¬ (send m ∈ outputsToActions{st} outs)
  {-
  sendMsg∉actions {[]} {st = st} outs≡ ()
  sendMsg∉actions {x ∷ outs} {st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st x) m∈acts
  ... | Left m∈[]
    with isOutputMsg? x
  ...| no  proof = outputToActions-sendMsg∉actions {out = x} {st = st} (λ x₁ → proof (silly x₁)) m∈[]
  ...| yes proof = ⊥-elim {! filter-some  and proof and 0 < length xs → xs ≢ [] !}
  sendMsg∉actions {x ∷ outs} {st = st} outs≡ m∈acts | Right m∈acts'
    with isOutputMsg? x
  ...| no  proof = sendMsg∉actions{outs = outs}{st = st} {! outs≡ !} m∈acts'
  ...| yes proof = {!proof!}
  -}

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

  sendVote∈actions'
    : ∀ {vm m pids outs st} → SendVote vm pids ∷ [] ≡ List-filter isOutputMsg? outs
      → send m ∈ outputsToActions{st} outs
      → m ≡ V vm
  sendVote∈actions' {outs = (BroadcastProposal x rcvrs) ∷ outs}{st = st} outs≡ m∈acts
    with Any-++⁻ (outputToActions st (BroadcastProposal x rcvrs)) m∈acts
  ... | Right m∈acts' = ⊥-elim (case outs≡ of λ ())
  ... | Left m∈[]     = ⊥-elim (case cong head outs≡ of λ ())
  sendVote∈actions' {pids = pids} {(BroadcastSyncInfo x rcvrs) ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions'{pids = pids} {outs} {st} (case cong head outs≡ of λ ()) m∈acts
  sendVote∈actions' {outs = LogErr x ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions'{outs = outs}{st = st} outs≡ m∈acts
  sendVote∈actions' {outs = LogInfo x ∷ outs}{st = st} outs≡ m∈acts =
    sendVote∈actions'{outs = outs}{st = st} outs≡ m∈acts
  sendVote∈actions' {vm}{m}{outs = SendVote vm“ pids' ∷ outs}{st = st} outs≡ m∈acts
    with ∷-injective outs≡
  ...| refl , tl≡
    with Any-++⁻ (List-map (const (send (V vm“))) pids') m∈acts
  ...| Right m∈[] = ⊥-elim (xxx {st} {m} {outs} m∈[] (sym tl≡))
       where
         xxx : ∀ {st m outs1} → send m ∈ outputsToActions {st} outs1 → ¬ NoneOfKind outs1 isOutputMsg?
         xxx {outs1 = []} ()
         xxx {outs1 = BroadcastProposal x x₁ ∷ _} _         = λ ()
         xxx {outs1 = BroadcastSyncInfo x x₁ ∷ _} _         = λ ()
         xxx {outs1 = LogErr x ∷ os}              send∈acts = obm-dangerous-magic!  -- TODO-1: I think we already have something close to this?
         xxx {outs1 = LogInfo x ∷ os}             send∈acts = obm-dangerous-magic!
         xxx {outs1 = SendVote x x₁ ∷ _} _                  = λ ()

  ... | Left m∈acts' = help pids' m∈acts'
    where
    help : ∀ pids → send m ∈ List-map (const (send (V vm“))) pids → m ≡ V vm“
    help (_ ∷ pids) (here refl) = refl
    help (_ ∷ pids) (there m∈acts) = help pids m∈acts

  sendVote∈actions
    : ∀ {vm vm' pids outs st} → SendVote vm pids ∷ [] ≡ List-filter isOutputMsg? outs
      → send (V vm') ∈ outputsToActions{st} outs
      → vm' ≡ vm
  sendVote∈actions {vm} {vm'} {pids} {outs} {st} outs≡ send∈ = let m = V vm' in
     V-inj $ sendVote∈actions' {vm} {V vm'} {pids} {outs} {st} outs≡ send∈ 
