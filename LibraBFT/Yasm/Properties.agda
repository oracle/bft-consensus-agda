{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Yasm.Base as LYB

-- This module provides some definitions and properties that facilitate
-- proofs of properties about a distributed system modeled by Yasm.System
-- paramaterized by some SystemParameters.

module LibraBFT.Yasm.Properties
   (ℓ-EC        : Level)
   (EpochConfig : Set ℓ-EC)
   (epoch       : EpochConfig → Epoch)
   (authorsN    : EpochConfig → ℕ)
   (parms       : LYB.SystemParameters ℓ-EC EpochConfig epoch authorsN)
   -- In addition to the parameters used by the rest of the system model, this module
   -- needs to relate Members to PKs and PeerIds, so that StepPeerState-AllValidParts
   -- can be defined.  This enables the application to prove that honest peers sign
   -- new messages only for their own public key.  The system model does not know that
   -- directly.
   (senderPKOK  : (ec : EpochConfig) → PK → LYB.SystemParameters.PeerId parms → Set)
  where
 open LYB.SystemParameters parms
 open import LibraBFT.Yasm.AvailableEpochs PeerId ℓ-EC EpochConfig epoch authorsN
             using (AvailableEpochs) renaming (lookup'' to EC-lookup)
 import      LibraBFT.Yasm.AvailableEpochs PeerId ℓ-EC EpochConfig epoch authorsN
             as AE
 open import LibraBFT.Yasm.Base   ℓ-EC EpochConfig epoch authorsN
 open import LibraBFT.Yasm.System ℓ-EC EpochConfig epoch authorsN parms
 open import Util.FunctionOverride PeerId _≟PeerId_

 -- A ValidPartForPK collects the assumptions about what a /part/ in the outputs of an honest verifier
 -- satisfies: (i) the epoch field is consistent with the existent epochs and (ii) the verifier is
 -- a member of the associated epoch config, and (iii) has the given PK in that epoch.
 record ValidSenderForPK {e}(𝓔s : AvailableEpochs e)(part : Part)(sender : PeerId)(pk : PK) : Set ℓ-EC where
   constructor mkValidSenderForPK
   field
     vp-epoch           : part-epoch part < e
     vp-ec              : EpochConfig
     vp-ec-≡            : AE.lookup'' 𝓔s vp-epoch ≡ vp-ec
     vp-sender-ok       : senderPKOK vp-ec pk sender
 open ValidSenderForPK public

 -- A valid part remains valid when new epochs are added
 ValidSenderForPK-stable-epoch : ∀{e part α pk}{𝓔s : AvailableEpochs e}(𝓔 : EpochConfigFor e)
                               → ValidSenderForPK 𝓔s part α pk
                               → ValidSenderForPK (AE.append 𝓔 𝓔s) part α pk
 ValidSenderForPK-stable-epoch {pk = pk} {𝓔s = 𝓔s} 𝓔 (mkValidSenderForPK e ec refl vpk) = record
   { vp-epoch           = ≤-step e
   ; vp-ec              = ec
   ; vp-ec-≡            = AE.lookup''-≤-step-lemma 𝓔s 𝓔 e
   ; vp-sender-ok       = vpk
   }

 -- A valid part remains valid
 ValidSenderForPK-stable : ∀{e e' α}{st : SystemState e}{st' : SystemState e'}
                    → Step* st st' → ∀{part pk}
                    → ValidSenderForPK (availEpochs st) part α pk
                    → ValidSenderForPK (availEpochs st') part α pk
 ValidSenderForPK-stable step-0 v = v
 ValidSenderForPK-stable (step-s st (step-epoch 𝓔)) v
   = ValidSenderForPK-stable-epoch 𝓔 (ValidSenderForPK-stable st v)
 ValidSenderForPK-stable (step-s st (step-peer _)) v
   = ValidSenderForPK-stable st v

 sameEpoch⇒sameEC : ∀ {e p1 p2 α1 α2 pk1 pk2}{𝓔s : AvailableEpochs e}
                    → (vp1 : ValidSenderForPK 𝓔s p1 α1 pk1)
                    → (vp2 : ValidSenderForPK 𝓔s p2 α2 pk2)
                    → part-epoch p1 ≡ part-epoch p2
                    → vp-ec vp1 ≡ vp-ec vp2
 sameEpoch⇒sameEC {𝓔s = 𝓔s} vp1 vp2 parts≡ =
   trans (sym (vp-ec-≡ vp1))
         (trans (AE.lookup-𝓔s-injective 𝓔s (vp-epoch vp1) (vp-epoch vp2) parts≡)
                (vp-ec-≡ vp2))

 -- TODO-1 : prove it
 postulate
   ValidSenderForPK⇒ep≡ : ∀ {e p1 p2 α1 pk} {𝓔s : AvailableEpochs e}
                        → WithVerSig pk p1 → WithVerSig pk p2
                        → part-epoch p1 ≡ part-epoch p2
                        → ValidSenderForPK 𝓔s p1 α1 pk
                        → ValidSenderForPK 𝓔s p2 α1 pk

 -- We say that an implementation produces only valid parts iff all parts of every message in the
 -- output of a 'StepPeerState' are either: (i) a valid new part (i.e., the part is valid and no
 -- message with the same signature has been sent previously), or (ii) a message has been sent
 -- with the same signature.
 StepPeerState-AllValidParts : Set ℓ-EC
 StepPeerState-AllValidParts = ∀{e s m part pk initd' outs}{α}{𝓔s : AvailableEpochs e}{st : SystemState e}
   → (r : ReachableSystemState st)
   → Meta-Honest-PK pk
   → StepPeerState α 𝓔s (msgPool st) (initialised st) (peerStates st α) initd' (s , outs)
   → m ∈ outs → part ⊂Msg m → (ver : WithVerSig pk part)
   → (ValidSenderForPK 𝓔s part α pk × ¬ (MsgWithSig∈ pk (ver-signature ver) (msgPool st)))
   ⊎ MsgWithSig∈ pk (ver-signature ver) (msgPool st)

 -- A /part/ was introduced by a specific step when:
 IsValidNewPart : ∀{e e'}{pre : SystemState e}{post : SystemState e'} → Signature → PK → Step pre post → Set ℓ-EC
 IsValidNewPart _ _ (step-epoch _) = Lift (ℓ-EC) ⊥
 -- said step is a /step-peer/ and
 IsValidNewPart {pre = pre} sig pk (step-peer {pid = pid} pstep)
    -- the part has never been seen before
    = ReachableSystemState pre
    × ¬ (MsgWithSig∈ pk sig (msgPool pre))
    × Σ (MsgWithSig∈ pk sig (msgPool (StepPeer-post pstep)))
        (λ m → ValidSenderForPK (availEpochs pre) (msgPart m) (msgSender m) pk)

 -- When we can prove that the implementation provided by 'parms' at the
 -- top of this module satisfies 'StepPeerState-AllValidParts', we can
 -- prove a number of useful structural properties:

 -- TODO-2: Refactor into a file (LibraBFT.Yasm.Properties.Structural) later on
 -- if this grows too large.
 module Structural (sps-avp      : StepPeerState-AllValidParts) where

     -- We can unwind the state and highlight the step where a part was
     -- originally sent. This 'unwind' function combined with Any-Step-elim
     -- enables a powerful form of reasoning. The 'honestVoteEpoch' below
     -- exemplifies this well.
     unwind : ∀{e}{st : SystemState e}(tr : ReachableSystemState st)
            → ∀{p m σ pk} → Meta-Honest-PK pk
            → p ⊂Msg m → (σ , m) ∈ msgPool st → (ver : WithVerSig pk p)
            → Any-Step (IsValidNewPart (ver-signature ver) pk) tr
     unwind (step-s tr (step-epoch _))    hpk p⊂m m∈sm sig
       = step-there (unwind tr hpk p⊂m m∈sm sig)
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) hpk p⊂m m∈sm sig
       with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} m∈sm
     ...| inj₂ furtherBack = step-there (unwind tr hpk p⊂m furtherBack sig)
     ...| inj₁ thisStep
       with sp
     ...| step-cheat fm isCheat
       with thisStep
     ...| here refl
       with isCheat p⊂m sig
     ...| inj₁ abs    = ⊥-elim (hpk abs)
     ...| inj₂ sentb4
       with unwind tr {p = msgPart sentb4} hpk (msg⊆ sentb4) (msg∈pool sentb4) (msgSigned sentb4)
     ...| res rewrite msgSameSig sentb4 = step-there res
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) hpk p⊂m m∈sm sig
        | inj₁ thisStep
        | step-honest x
       with Any-satisfied-∈ (Any-map⁻ thisStep)
     ...| (m , refl , m∈outs)
       with sps-avp tr hpk x m∈outs p⊂m sig
     ...| inj₂ sentb4 with unwind tr {p = msgPart sentb4} hpk (msg⊆ sentb4) (msg∈pool sentb4) (msgSigned sentb4)
     ...| res rewrite msgSameSig sentb4 = step-there res
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) {p} hpk p⊂m m∈sm sig
        | inj₁ thisStep
        | step-honest x
        | (m , refl , m∈outs)
        | inj₁ (valid-part , notBefore) =
               step-here tr (tr , notBefore , MsgWithSig∈-++ˡ (mkMsgWithSig∈ _ _ p⊂m β thisStep sig refl)
                                       , valid-part)

     -- Unwind is inconvenient to use by itself because we have to do
     -- induction on Any-Step-elim. The 'honestPartValid' property below
     -- provides a fairly general result conveniently: for every part
     -- verifiable with an honest PK, there is a msg with the same
     -- signature that is valid for some pid.

     honestPartValid : ∀ {e st} → ReachableSystemState {e} st → ∀ {pk nm v sender}
                     → Meta-Honest-PK pk
                     → v ⊂Msg nm → (sender , nm) ∈ msgPool st → (ver : WithVerSig pk v)
                     → Σ (MsgWithSig∈ pk (ver-signature ver) (msgPool st))
                         (λ msg → (ValidSenderForPK (availEpochs st) (msgPart msg) (msgSender msg) pk))
     honestPartValid {e} {st} r {pk = pk} hpk v⊂m m∈pool ver
     -- We extract two pieces of important information from the place where the part 'v'
     -- was first sent: (a) there is a message with the same signature /in the current pool/
     -- and (b) its epoch is less than e.
        = Any-Step-elim (λ { {st = step-epoch _} ()
                           ; {st = step-peer {pid = pid} ps} (_ , _ , new , valid) tr
                             →  MsgWithSig∈-Step* tr new
                                , ValidSenderForPK-stable tr (subst (λ P → ValidSenderForPK _ P (msgSender (MsgWithSig∈-Step* tr new)) pk)
                                                                         (MsgWithSig∈-Step*-part tr new)
                                                                         (subst (λ sndr → ValidSenderForPK _ _ sndr pk)
                                                                                (MsgWithSig∈-Step*-sender tr new)
                                                                                valid))
                           })
                        (unwind r hpk v⊂m m∈pool ver)

     -- Unforgeability is also an important property stating that every part that is
     -- verified with an honest public key has either been sent by α or is a replay
     -- of another message sent before.
     ext-unforgeability'
       : ∀{e α m part pk}{st : SystemState e} → ReachableSystemState st
       -- If a message m has been sent by α, containing part
       → (α , m) ∈ msgPool st → part ⊂Msg m
       -- And the part can be verified with an honest public key,
       → (sig : WithVerSig pk part) → Meta-Honest-PK pk
       -- then either the part is a valid part by α (meaning that α can
       -- sign the part itself) or a message with the same signature has
       -- been sent previously.
       → ValidSenderForPK (availEpochs st) part α pk
       ⊎ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     ext-unforgeability' (step-s st (step-epoch 𝓔)) m∈sm p⊆m sig hpk
       = ⊎-map (ValidSenderForPK-stable-epoch 𝓔) id (ext-unforgeability' st m∈sm p⊆m sig hpk)
     ext-unforgeability' {part = part} (step-s st (step-peer {pid = β} {outs = outs} {pre = pre} sp)) m∈sm p⊆m sig hpk
       with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} m∈sm
     ...| inj₂ furtherBack = MsgWithSig∈-++ʳ <⊎$> (ext-unforgeability' st furtherBack p⊆m sig hpk)
     ...| inj₁ thisStep
       with sp
     ...| step-cheat fm isCheat
       with thisStep
     ...| here refl
       with isCheat p⊆m sig
     ...| inj₁ abs    = ⊥-elim (hpk abs)
     ...| inj₂ sentb4 = inj₂ (MsgWithSig∈-++ʳ sentb4)
     ext-unforgeability' {α = α} {m = m} {part = part} (step-s st (step-peer {pid = β} {outs = outs} {pre = pre} sp)) m∈sm p⊆m sig hpk
        | inj₁ thisStep
        | step-honest x
       with Any-satisfied-∈ (Any-map⁻ thisStep)
     ...| (m , refl , m∈outs) = ⊎-map proj₁ MsgWithSig∈-++ʳ (sps-avp st hpk x m∈outs p⊆m sig)

     -- The ext-unforgeability' property can be collapsed in a single clause.

     -- TODO-2: so far, ext-unforgeability is used only to get a MsgWithSig∈ that is passed to
     -- msgWithSigSentByAuthor, which duplicates some of the reasoning in the proof of
     -- ext-unforgeability'; should these properties possibly be combined into one simpler proof?
     ext-unforgeability
       : ∀{e α₀ m part pk}{st : SystemState e} → ReachableSystemState st
       → (α₀ , m) ∈ msgPool st → part ⊂Msg m
       → (sig : WithVerSig pk part) → Meta-Honest-PK pk
       → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     ext-unforgeability {_} {α₀} {m} {st = st} rst m∈sm p⊂m sig hpk
       with ext-unforgeability' rst m∈sm p⊂m sig hpk
     ...| inj₁ p
        = mkMsgWithSig∈ _ _ p⊂m α₀ m∈sm sig refl
     ...| inj₂ sentb4 = sentb4

     ¬cheatForgeNew : ∀ {e pid pk vsig mst outs m}{st : SystemState e}
                    → (sp : StepPeer st pid mst outs)
                    → outs ≡ m ∷ []
                    → (ic : isCheat sp)
                    → Meta-Honest-PK pk
                    → MsgWithSig∈ pk vsig ((pid , m) ∷ msgPool st)
                    → MsgWithSig∈ pk vsig (msgPool st)
     ¬cheatForgeNew sc@(step-cheat fm isCheat) refl _ hpk mws
        with msg∈pool mws
     ...| there m∈pool = mkMsgWithSig∈ (msgWhole mws) (msgPart mws) (msg⊆ mws) (msgSender mws) m∈pool (msgSigned mws) (msgSameSig mws)
     ...| here m∈pool
        with isCheat (subst (msgPart mws ⊂Msg_) (cong proj₂ m∈pool) (msg⊆ mws)) (msgSigned mws)
     ...| inj₁ dis = ⊥-elim (hpk dis)
     ...| inj₂ mws' rewrite msgSameSig mws = mws'



     msgWithSigSentByAuthor : ∀ {e pk sig}{st : SystemState e}
                            → ReachableSystemState st
                            → Meta-Honest-PK pk
                            → MsgWithSig∈ pk sig (msgPool st)
                            → Σ (MsgWithSig∈ pk sig (msgPool st))
                                λ mws → ValidSenderForPK (availEpochs st) (msgPart mws) (msgSender mws) pk
     msgWithSigSentByAuthor step-0 _ ()
     msgWithSigSentByAuthor (step-s {pre = pre} preach (step-epoch 𝓔)) hpk mws
       rewrite step-epoch-does-not-send pre 𝓔
          with msgWithSigSentByAuthor preach hpk mws
     ...| mws' , vpb =  mws' , ValidSenderForPK-stable {st = pre} (step-s step-0 (step-epoch 𝓔)) vpb
     msgWithSigSentByAuthor {pk = pk} (step-s {pre = pre} preach (step-peer theStep@(step-cheat fm cheatCons))) hpk mws
        with (¬cheatForgeNew theStep refl unit hpk mws)
     ...| mws'
        with msgWithSigSentByAuthor preach hpk mws'
     ...| mws'' , vpb'' = MsgWithSig∈-++ʳ mws'' , vpb''
     msgWithSigSentByAuthor {e} (step-s {pre = pre} preach (step-peer {pid = pid} {outs = outs} (step-honest sps))) hpk mws
       with Any-++⁻ (List-map (pid ,_) outs) {msgPool pre} (msg∈pool mws)
     ...| inj₂ furtherBack
       with msgWithSigSentByAuthor preach hpk (MsgWithSig∈-transp mws furtherBack)
     ...| mws' , vpb' =  MsgWithSig∈-++ʳ mws' , vpb'

     msgWithSigSentByAuthor {e} (step-s {pre = pre} preach (step-peer {pid = pid} {outs = outs} (step-honest sps))) hpk mws
        | inj₁ thisStep
        with Any-satisfied-∈ (Any-map⁻ thisStep)
     ...| (m' , refl , m∈outs)
        with sps-avp preach hpk sps m∈outs (msg⊆ mws) (msgSigned mws)
     ...| inj₁ (vpbα₀ , _) = mws , vpbα₀
     ...| inj₂ mws'
        with msgWithSigSentByAuthor preach hpk mws'
     ...| mws'' , vpb'' rewrite sym (msgSameSig mws) = MsgWithSig∈-++ʳ mws'' , vpb''


     newMsg⊎msgSentB4 :  ∀ {e pk v m pid sndr st' outs} {st : SystemState e}
                   → (r : ReachableSystemState st)
                   → (stP : StepPeer st pid st' outs)
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → v ⊂Msg m → (sndr , m) ∈ msgPool (StepPeer-post stP)
                   → (m ∈ outs × ValidSenderForPK (availEpochs st) v pid pk
                      × ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool st)))
                     ⊎ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     newMsg⊎msgSentB4 {e} {pk} {v} {m} {pid} {sndr} {_} {outs} {st} r stP pkH sig v⊂m m∈post
        with Any-++⁻ (List-map (pid ,_) outs) m∈post
     ...| inj₂ m∈preSt = inj₂ (mkMsgWithSig∈ m v v⊂m sndr m∈preSt sig refl)
     ...| inj₁ nm∈outs
        with Any-map (cong proj₂) (Any-map⁻ nm∈outs)
     ...| m∈outs
        with stP
     ...| step-honest stH
        with sps-avp r pkH stH m∈outs v⊂m sig
     ...| inj₁ newVote = inj₁ (m∈outs , newVote)
     ...| inj₂ msb4    = inj₂ msb4
     newMsg⊎msgSentB4 {e} {pk} {v} {m} {pid} {sndr} {_} {outs} {st} r stP pkH sig v⊂m m∈post
        | inj₁ nm∈outs
        | here refl
        | step-cheat fm ic
          = let mws = mkMsgWithSig∈ m v v⊂m pid (here refl) sig refl
            in inj₂ (¬cheatForgeNew {st = st} (step-cheat fm ic) refl unit pkH mws)

 -- This could potentially be more general, for example covering the whole SystemState, rather than
 -- just one peer's state.  However, this would put more burden on the user and is not required so
 -- far.
 CarrierProp : Set₁
 CarrierProp = Part → PeerState → Set

 module _ (P   : CarrierProp) where

  record PropCarrier (pk : PK) (sig : Signature) {e} (st : SystemState e) : Set (ℓ-EC ℓ⊔ (ℓ+1 0ℓ)) where
    constructor mkCarrier
    field
      carrStReach : ReachableSystemState st -- Enables use of invariants when proving that steps preserve carrProp
      carrSent    : MsgWithSig∈ pk sig (msgPool st)
      carrValid   : ValidSenderForPK (availEpochs st) (msgPart carrSent) (msgSender carrSent) pk
      carrProp    : P (msgPart carrSent) (peerStates st (msgSender carrSent))
  open PropCarrier public

  PeerStepPreserves : Set (ℓ+1 ℓ0 ℓ⊔ ℓ-EC)
  PeerStepPreserves = ∀ {e initd' ps' outs pk sig}{pre : SystemState e}
                      → (r : ReachableSystemState pre)
                      → (pc : PropCarrier pk sig {e} pre)
                      → (sps : StepPeerState {e} (msgSender (carrSent pc))
                                                 (availEpochs pre)
                                                 (msgPool pre)
                                                 (initialised pre)
                                                 (peerStates pre (msgSender (carrSent pc)))
                                                 initd'
                                                 (ps' , outs))
                      → P (msgPart (carrSent pc)) ps'

  module _ (PSP : PeerStepPreserves) where

    Carrier-transp : ∀ {e' e'' pk sig} {pre : SystemState e'}{post : SystemState e''}
                   → (theStep : Step pre post)
                   → PropCarrier pk sig pre
                   → PropCarrier pk sig post
    Carrier-transp {pre = pre} {post} (step-epoch ec) (mkCarrier r mws vpk lvr) =
       mkCarrier (step-s r (step-epoch ec)) mws (ValidSenderForPK-stable-epoch ec vpk) lvr
    Carrier-transp {e' = e'} {pre = pre} {post} theStep@(step-peer {pid = pid} {st'} {pre = .pre} sps) pc@(mkCarrier r mws vpk prop)
       with step-s r theStep
    ...| postReach
       with sps
    ...| step-cheat fm isch = mkCarrier postReach (MsgWithSig∈-++ʳ mws) vpk
           (subst (λ ps → P (msgPart mws) (ps (msgSender mws))) (sym (cheatStepDNMPeerStates {pre = pre} (step-cheat fm isch) unit)) prop)
    -- PeerStates not changed by cheat steps
    ...| step-honest {st = st} sps'
       with msgSender mws ≟PeerId pid
    ...| no neq   = mkCarrier postReach (MsgWithSig∈-++ʳ mws) vpk
                              (subst (λ ps → P (msgPart mws) ps) (override-target-≢ {f = peerStates pre} neq) prop)
    ...| yes refl = mkCarrier postReach (MsgWithSig∈-++ʳ mws) vpk
                              (subst (λ ps → P (msgPart mws) ps) (sym override-target-≡) (PSP r pc sps'))
