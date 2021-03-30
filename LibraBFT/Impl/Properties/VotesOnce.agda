{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module proves the two "VotesOnce" proof obligations for our fake handler

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS

import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.Impl.Base.Types

open import LibraBFT.Impl.Consensus.Types hiding (EpochConfigFor)
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor.Properties  sha256 sha256-cr
open import LibraBFT.Impl.Handle                                          sha256 sha256-cr
open import LibraBFT.Impl.Handle.Properties                               sha256 sha256-cr
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Properties.Aux
open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm (ℓ+1 0ℓ) EpochConfig epochId authorsN ConcSysParms NodeId-PK-OK
open        Structural impl-sps-avp

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  postulate  -- TODO-2: prove.  Note that these are really just properties about the handler,
             -- but are currently wrapped up into properties about SystemState.  These should
             -- probably be "unbundled" and move to LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor
    newVoteSameEpochGreaterRound : ∀ {e 𝓔s pid pool ms s s' outs v m pk}
                                 → StepPeerState {e} pid 𝓔s pool ms s' outs
                                 → ms ≡ just s
                                 → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                                 → ¬ MsgWithSig∈ pk (ver-signature sig) pool
                                 → (v ^∙ vEpoch) ≡ (₋epEC s) ^∙ epEpoch
                                 × suc ((₋epEC s) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                                 × (v ^∙ vRound) ≡ ((₋epEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote

    -- Always true, so far, as no epoch changes.
    noEpochChangeYet : ∀ {e e'}{pre : SystemState e}{post : SystemState e'}{pid}{ppre ppost}
                        → Step pre post -- Might or might not be a step by pid
                        → Map-lookup pid (peerStates pre)  ≡ just ppre
                        → Map-lookup pid (peerStates post) ≡ just ppost
                        → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch

    epoch≡stepPeer : ∀ {e}{st : SystemState e}{pid s}
                   → ReachableSystemState st
                   → Map-lookup pid (peerStates st) ≡ just s
                   → (₋epEC s) ^∙ epEpoch ≡ epochId (α-EC (₋epEC s , ₋epEC-correct s))

    -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
    lastVoteRound-mono' : ∀ {e e'}{pre : SystemState e}{post : SystemState e'}{pid}{ppre ppost}
                        → Step pre post -- Might or might not be a step by pid
                        → Map-lookup pid (peerStates pre)  ≡ just ppre
                        → Map-lookup pid (peerStates post) ≡ just ppost
                        → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch
                        → (₋epEC ppre) ^∙ epLastVotedRound ≤ (₋epEC ppost) ^∙ epLastVotedRound

    honMsg∈pool⇒ValidSenderForPK :  ∀ {e pid pk v}{st : SystemState e}
                                 → (r : ReachableSystemState st)
                                 → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                                 → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                                 → ValidSenderForPK (availEpochs st) v pid pk

    pid≢⇒msgSent4 : ∀ {e pid pk v} {pid' s' outs}{st : SystemState e}
                  → (r : ReachableSystemState st)
                  → (stP : StepPeerState pid' (availEpochs st) (msgPool st)
                                         (Map-lookup pid' (peerStates st)) s' outs)
                  → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                  → MsgWithSig∈ pk (ver-signature sig)
                                (msgPool (StepPeer-post (step-honest stP)))
                  → ValidSenderForPK (availEpochs st) v pid pk
                  → pid ≢ pid'
                  → MsgWithSig∈ pk (ver-signature sig) (msgPool st)


  oldVoteRound≤lvr :  ∀ {e pid pk v s}{pre : SystemState e}
         → (r : ReachableSystemState pre)
         → Map-lookup pid (peerStates pre) ≡ just s
         → Meta-Honest-PK pk → (sig : WithVerSig pk v)
         → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
         → ValidSenderForPK (availEpochs pre) v pid pk
         → (₋epEC s) ^∙ epEpoch ≡ (v ^∙ vEpoch)
         → v ^∙ vRound ≤ (₋epEC s) ^∙ epLastVotedRound
  oldVoteRound≤lvr (step-s {e} {e'} {e''} r (step-epoch _)) lkp≡s pkH sig msv vspkv ep≡
      = let vspkvPre = honMsg∈pool⇒ValidSenderForPK r pkH sig msv
        in oldVoteRound≤lvr r lkp≡s pkH sig msv vspkvPre ep≡
  oldVoteRound≤lvr (step-s r (step-peer cheat@(step-cheat fm ch))) lkp≡s pkH sig msv vspkv ep≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     with msgSameSig msb4
  ...| refl
    rewrite cheatStepDNMPeerStates cheat unit
    = oldVoteRound≤lvr r lkp≡s pkH sig msb4 vspkv ep≡
  oldVoteRound≤lvr {pid = pid} {pre = pre} (step-s r step@(step-peer stPeer@(step-honest {pid'} {st} {outs} stP))) lkp≡s pkH sig msv vspkv ep≡
    with pid ≟ pid'
  ...| no imp =  let ms≡pre = pid≢DNMState r stP imp lkp≡s
                     mwssb4 = pid≢⇒msgSent4 r stP pkH sig msv vspkv imp
                    in oldVoteRound≤lvr r ms≡pre pkH sig mwssb4 vspkv ep≡
  ...| yes refl
     with stP
  ...| step-init _ refl = {!!} --oldVoteRound≤lvr r {!lkp≡s!} pkH sig msv vspkv {!!}
                            -- We cannot prove this yet because
                            -- initialEventProcessorAndMessages is faked for now.  We
                            -- need to establish rules for what initialization by a
                            -- peer pid does.  It must ensure that if pid's new
                            -- peerState is for epoch e and has lastVotedRound = r,
                            -- then pid has not previously sent any messages containing
                            -- votes for the epoch e and for a round higher than r
  ...| step-msg {_ , nm} {ms} {s} {s'} m∈pool ms≡ handle≡
      with Any-++⁻ (List-map (pid' ,_) outs) (msg∈pool msv)
  ...| inj₂ msb4
    with MsgWithSig∈-transp msv msb4
  ...| mwssb4
    with sameHonestSig⇒sameVoteData pkH sig (msgSigned mwssb4) (sym (msgSameSig mwssb4))
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre (step-s r step) hb)
  ...| inj₂ refl = let ep≡stP  = noEpochChangeYet step ms≡ lkp≡s
                       ep≡Vote = trans ep≡stP ep≡
                       lvr≤ = lastVoteRound-mono' step ms≡ lkp≡s ep≡stP
                   in ≤-trans (oldVoteRound≤lvr r ms≡ pkH sig mwssb4 vspkv ep≡Vote) lvr≤
  oldVoteRound≤lvr {pid = pid} {s = s} {pre = pre} (step-s r step@(step-peer stPeer@(step-honest {pid'} {st} {outs} stP))) lkp≡s pkH sig msv vspkv ep≡
     | yes refl
     | step-msg {nm} {ms} {s₁} {s'} m∈pool ms≡ handle≡
     | inj₁ nm∈outs
     with Any-map (cong proj₂) (Any-map⁻ nm∈outs)
  ...| m∈outs
    with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb   = ⊥-elim (PerState.meta-sha256-cr pre (step-s r step) hb)
  ...| inj₂ refl
     with impl-sps-avp r pkH stP m∈outs (msg⊆ msv) (msgSigned msv)
  ...| inj₁ (vpk , vNew)
     rewrite eventProcessorPostSt r stP lkp≡s
      = let nvr = newVoteSameEpochGreaterRound stP ms≡ (msg⊆ msv) m∈outs (msgSigned msv) vNew
        in ≡⇒≤ ((proj₂ ∘ proj₂) nvr)
  ... | inj₂ mwssb4
    rewrite msgSameSig msv
    with sameHonestSig⇒sameVoteData pkH sig (msgSigned mwssb4) (sym (msgSameSig mwssb4))
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre (step-s r step) hb)
  ...| inj₂ refl = let ep≡stP  = noEpochChangeYet step ms≡ lkp≡s
                       ep≡Vote = trans ep≡stP ep≡
                       lvr≤ = lastVoteRound-mono' step ms≡ lkp≡s ep≡stP
                   in ≤-trans (oldVoteRound≤lvr r ms≡ pkH sig mwssb4 vspkv ep≡Vote) lvr≤



  vo₁ : VO.ImplObligation₁
  vo₁ r (step-init _ refl) _ _ m∈outs _ _ _ _ _ _ _ _ = ⊥-elim (¬Any[] m∈outs)
  vo₁ {pid' = pid'} r (step-msg {_ , nm} {ms} {s} m∈pool ms≡ hndl≡) {v} {m} {v'} {m'} pkH v⊂m m∈outs sv ¬msb vspkv v'⊂m' m'∈pool sv' ep≡ r≡
    rewrite cong proj₂ hndl≡
    with nm
  ...| P pm
    with m∈outs
  ...| here refl
    with v⊂m
  ... | vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                      vspkv' = ValidSenderForPK⇒ep≡ sv sv' ep≡ vspkv
                      ep≡stP = trans (epoch≡stepPeer r ms≡) ep≡
                      rv'<rv = oldVoteRound≤lvr r ms≡ pkH sv' m'mwsb vspkv' ep≡stP
                  in ⊥-elim (<⇒≢ (s≤s rv'<rv) (sym r≡))
  ... | vote∈qc vs∈qc v≈rbld (inV qc∈m)
     rewrite cong ₋vSignature v≈rbld
    = ⊥-elim (¬msb (qcVotesSentB4 r ms≡ qc∈m refl vs∈qc))


  vo₂ : VO.ImplObligation₂
  vo₂ _ (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₂ {pk = pk} {st} r (step-msg {pid , nm} {s = ps} _ ps≡ hndl≡) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig vnew vpk v'⊂m' m'∈outs sig' v'new vpk' es≡ rnds≡
     rewrite cong proj₂ hndl≡
    with nm
  ...| P msg
    with msgsToSendWereSent {pid} {0} {P msg} {m} {ps} m∈outs
  ...| vm , refl , vmSent
    with msgsToSendWereSent1 {pid} {0} {msg} {vm} {ps} vmSent
  ...| _ , v∈outs
     rewrite SendVote-inj-v  (Any-singleton⁻ v∈outs)
           | SendVote-inj-si (Any-singleton⁻ v∈outs)
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {msg} {ps} {vm} v∈outs
     = ⊥-elim (vnew (qcVotesSentB4 r ps≡ qc∈m refl vs∈qc))
  ...| vote∈vm {si}
     with m'
  ...| P _ = ⊥-elim (P≢V (Any-singleton⁻ m'∈outs))
  ...| C _ = ⊥-elim (C≢V (Any-singleton⁻ m'∈outs))
  ...| V vm'
       -- Because the handler sends only one message, the two VoteMsgs vm and vm' are the same
     rewrite V-inj (trans (Any-singleton⁻ m'∈outs) (sym (Any-singleton⁻ m∈outs)))
     with v'⊂m'
       -- Both votes are the vote in the (single) VoteMsg, so their biIds must be the same
  ...| vote∈vm = refl
       -- Here we use the same reasoning as above to show that v' is not new
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {msg} {ps} {vm} v∈outs
     = ⊥-elim (v'new (qcVotesSentB4 r ps≡ qc∈m refl vs∈qc))
