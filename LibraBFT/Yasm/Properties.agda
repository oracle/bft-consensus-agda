{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Yasm.Base as LYB

-- This module provides some definitions and properties that facilitate
-- proofs of properties about a distributed system modeled by Yasm.System
-- paramaterized by some SystemParameters.

module LibraBFT.Yasm.Properties
   (NodeId      : Set)
   (ℓ-EC        : Level)
   (EpochConfig : Set ℓ-EC)
   (epochId     : EpochConfig → EpochId)
   (authorsN    : EpochConfig → ℕ)
   (getPubKey   : (ec : EpochConfig) → LYB.Member NodeId ℓ-EC EpochConfig epochId authorsN ec → PK)
   (parms       : LYB.SystemParameters NodeId ℓ-EC EpochConfig epochId authorsN)
  where
 open import LibraBFT.Yasm.AvailableEpochs NodeId ℓ-EC EpochConfig epochId authorsN
             using (AvailableEpochs) renaming (lookup'' to EC-lookup)
 import      LibraBFT.Yasm.AvailableEpochs NodeId ℓ-EC EpochConfig epochId authorsN
             as AE
 open import LibraBFT.Yasm.Base            NodeId ℓ-EC EpochConfig epochId authorsN
 open import LibraBFT.Yasm.System NodeId ℓ-EC EpochConfig epochId authorsN parms
 open LYB.SystemParameters parms

 -- A ValidPartForPK collects the assumptions about what a /part/ in the outputs of an honest verifier
 -- satisfies: (i) the epoch field is consistent with the existent epochs and (ii) the verifier is
 -- a member of the associated epoch config, and (iii) has the given PK in that epoch.
 record ValidPartForPK {e}(𝓔s : AvailableEpochs e)(part : Part)(pk : PK) : Set ℓ-EC where
   constructor mkValidPartForPK
   field
     vp-epoch           : part-epoch part < e
     vp-ec              : EpochConfig
     vp-ec-≡            : AE.lookup'' 𝓔s vp-epoch ≡ vp-ec
     vp-member          : Member vp-ec
     vp-key             : getPubKey vp-ec vp-member ≡ pk
 open ValidPartForPK public

 -- A valid part remains valid when new epochs are added
 ValidPartForPK-stable-epoch : ∀{e part pk}{𝓔s : AvailableEpochs e}(𝓔 : EpochConfigFor e)
                          → ValidPartForPK 𝓔s part pk
                          → ValidPartForPK (AE.append 𝓔 𝓔s) part pk
 ValidPartForPK-stable-epoch {pk = pk} {𝓔s} 𝓔 (mkValidPartForPK e ec refl emem vpk) = record
   { vp-epoch           = ≤-step e
   ; vp-ec              = ec
   ; vp-ec-≡            = AE.lookup''-≤-step-lemma 𝓔s 𝓔 e
   ; vp-member          = emem
   ; vp-key             = vpk
   }

 -- A valid part remains valid
 ValidPartForPK-stable : ∀{e e'}{st : SystemState e}{st' : SystemState e'}
                    → Step* st st' → ∀{part pk}
                    → ValidPartForPK (availEpochs st) part pk
                    → ValidPartForPK (availEpochs st') part pk
 ValidPartForPK-stable step-0 v = v
 ValidPartForPK-stable (step-s st (step-epoch 𝓔)) v
   = ValidPartForPK-stable-epoch 𝓔 (ValidPartForPK-stable st v)
 ValidPartForPK-stable (step-s st (step-peer _)) v
   = ValidPartForPK-stable st v

 -- We say that an implementation produces only valid parts iff all parts of every message in the
 -- output of a 'StepPeerState' are either: (i) a valid new part (i.e., the part is valid and has
 -- not been included in a previously sent message with the same signature), or (ii) the part been
 -- included in a previously sent message with the same signature.
 StepPeerState-AllValidParts : Set ℓ-EC
 StepPeerState-AllValidParts = ∀{e s m part pk outs α}{𝓔s : AvailableEpochs e}{st : SystemState e}
   → (r : ReachableSystemState st)
   → Meta-Honest-PK pk
   → StepPeerState α 𝓔s (msgPool st) (Map-lookup α (peerStates st)) s outs
   → m ∈ outs → part ⊂Msg m → (ver : WithVerSig pk part)
                                 -- NOTE: this doesn't DIRECTLY imply that nobody else has sent a
                                 -- message with the same signature just that the author of the part
                                 -- hasn't.
   → (ValidPartForPK 𝓔s part pk × ¬ (MsgWithSig∈ pk (ver-signature ver) (msgPool st)))
   ⊎ MsgWithSig∈ pk (ver-signature ver) (msgPool st)

 -- A /part/ was introduced by a specific step when:
 IsValidNewPart : ∀{e e'}{pre : SystemState e}{post : SystemState e'} → Signature → PK → Step pre post → Set ℓ-EC
 IsValidNewPart _ _ (step-epoch _) = Lift ℓ-EC ⊥
 -- said step is a /step-peer/ and
 IsValidNewPart {pre = pre} sig pk (step-peer pstep)
    -- the part has never been seen before
    = ¬ (MsgWithSig∈ pk sig (msgPool pre))
    × Σ (MsgWithSig∈ pk sig (msgPool (StepPeer-post pstep)))
        (λ m → ValidPartForPK (availEpochs pre) (msgPart m) pk)

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
               step-here tr (notBefore , MsgWithSig∈-++ˡ (mkMsgWithSig∈ _ _ p⊂m β thisStep sig refl)
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
                         (λ msg → (ValidPartForPK (availEpochs st) (msgPart msg) pk))
     honestPartValid {e} {st} r {pk = pk} hpk v⊂m m∈pool ver
     -- We extract two pieces of important information from the place where the part 'v'
     -- was first sent: (a) there is a message with the same signature /in the current pool/
     -- and (b) its epoch is less than e.
        = Any-Step-elim (λ { {st = step-epoch _} ()
                           ; {st = step-peer ps} (_ , new , valid) tr
                             →  MsgWithSig∈-Step* tr new
                                , ValidPartForPK-stable tr
                                    (subst (λ P → ValidPartForPK _ P pk)
                                           (MsgWithSig∈-Step*-part tr new) valid)
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
       → ValidPartForPK (availEpochs st) part pk
       ⊎ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     ext-unforgeability' (step-s st (step-epoch 𝓔)) m∈sm p⊆m sig hpk
       = ⊎-map (ValidPartForPK-stable-epoch 𝓔) id (ext-unforgeability' st m∈sm p⊆m sig hpk)
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
     ext-unforgeability' {m = m} {part = part} (step-s st (step-peer {pid = β} {outs = outs} {pre = pre} sp)) m∈sm p⊆m sig hpk
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
                                λ mws → ValidPartForPK (availEpochs st) (msgPart mws) pk
     msgWithSigSentByAuthor step-0 _ ()
     msgWithSigSentByAuthor (step-s {pre = pre} preach (step-epoch 𝓔)) hpk mws
       rewrite step-epoch-does-not-send pre 𝓔
          with msgWithSigSentByAuthor preach hpk mws
     ...| mws' , vpb =  mws' , ValidPartForPK-stable {st = pre} (step-s step-0 (step-epoch 𝓔)) vpb
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
