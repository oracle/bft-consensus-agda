{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module proves the two "VotesOnce" proof obligations for our fake handler


-- Note that the proofs in this file were broken by the changes to eliminate EpochConfigs from the
-- system model and to move towards more realistic initialisation.  Below some parts of the proofs
-- are commented out and some holes are left to enable exploring where the proof breaks down.

-- UPDATE: we have changed PeersCanSignFor (and the its generic counterpart ValidPartBy) to be
-- functions of SystemState, rather than PeerState, and these changes have NOT been propagated to
-- this file.

-- One key issue is that, with the new definitions, whether a step by a peer can sign a message
-- for a PK in a particular epoch is a function of the post state, rather than a function of the
-- available EpochConfigs in the system state as it was before.  This means that a peer can learn
-- of a new EpochConfig during a step (either from GenesisInfo in step-init or, eventually, by
-- committing an epoch-changing transaction and adding another EpochConfig as a result).  Thus,
-- unlike before, it is possible for a peer step to sign and send a new message, even though
-- PeerCanSignForPK did not hold in its prestate.  For that reason, the ImplObligation₁ now
-- receives evidence that it can sign in the step's post state (in the form of PeerCanSignForPK
-- (StepPeer-post {pre = pre} (step-honest sps)) v pid pk), whereas previously, it received
-- evidence that it could do so in the step's prestate (in the form of ValidSenderForPK
-- (availEpochs pre) v pid pk).

-- I have fixed various things broken by the changes where it was easy to do so, and created holes
-- (mostly containing whatever was there previously) so that the file type checks.  However, I am
-- not pushing further on this at the moment.  There are still significant issues to resolve to
-- come up with a VotesOnce proof without using unwind.

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS

import      LibraBFT.Concrete.Properties.VotesOnce as VO

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Consensus.RoundManager.Properties sha256 sha256-cr
open import LibraBFT.Impl.Handle.Properties                 sha256 sha256-cr
open import LibraBFT.Impl.Properties.Aux
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        WithSPS impl-sps-avp
open        Structural impl-sps-avp
open import LibraBFT.Impl.Properties.VotesOnce

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnceDirect where


  newVoteEpoch≡⇒GreaterRound : ∀ {st : SystemState}{pid s' outs v m pk}
                               → ReachableSystemState st
                               → StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs)
                               → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                               → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                               → v ^∙ vEpoch ≡ (₋rmEC s') ^∙ rmEpoch
                               → v ^∙ vRound ≡ (₋rmEC s') ^∙ rmLastVotedRound
  newVoteEpoch≡⇒GreaterRound r (step-msg {_ , P pm} _ pinit) v⊂m (here refl) sig vnew ep≡
     with v⊂m
  ...| vote∈vm = refl
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
       = ⊥-elim (vnew (qcVotesSentB4 r pinit refl qc∈m refl vs∈qc))

  open PeerCanSignForPK

  peerCanSignSameS : ∀ {pid v pk s s'}
                   → PeerCanSignForPK s v pid pk
                   → s' ≡ s
                   → PeerCanSignForPK s' v pid pk
  peerCanSignSameS pcs refl = pcs

  -- NOTE: the (ab)use of the temporary "bogus" properties (now eliminated) in the "proof" of
  -- peerCansign-msb4 below hides a significant issue.  Those properties were originally used in a
  -- context in which the peer has been initialised to show that a step by the peer does not
  -- change its number of epoch configs or actual epoch configs.  The usage here attempts to use
  -- those properties to reason "backwards" across a step, with no guarantee that the peer was
  -- initialised in the prestate.  Thus, the properties that have replaced the bogus ones and have
  -- been proved (noEpochChangeSPS₁ and noEpochChangeSPS₂) do not work here.

  -- The key reason that this property holds is the MsgWithSig∈, which says that *some* peer has
  -- sent a message with the same signature in the prestate.  But this does not (directly) imply
  -- that pid sent it.  Another peer might have observed the signature being sent previously and
  -- resend it.  The whole point of unwind is to go back to the *first* time the signature was sent,
  -- at which point we can capture that (because pk is honest), the sender must be valid to sign for
  -- that pk in that epoch, and then we can use injectivity of PKs to conclude that this sender was
  -- pid (see line 229-233 in VotesOnce.agda).

  -- I think it's possible to capture everything we need in a property that can be proved directly
  -- by induction (as opposed to using unwind), but I also think this exercise has shown that it
  -- will involve much of the same complexity, and perhaps be more difficult overall.  Maybe
  -- something like the following could be proved inductively, and then used together with
  -- injectivity properties as mentioned above to determine that the two pids are the same.

  postulate
   MsgWithSig⇒ValidSenderInitialised :
     ∀ {st pk v}
     → ReachableSystemState st
     → Meta-Honest-PK pk
     → MsgWithSig∈ pk (₋vSignature v) (msgPool st)
     → ∃[ pid ] ( initialised st pid ≡ initd
                × PeerCanSignForPK st v pid pk )


  peerCanSign-Msb4 : ∀ {pid v s' outs pk}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeer st pid s' outs)
                    → PeerCanSignForPK (StepPeer-post stP) v pid pk
                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                    → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                    → PeerCanSignForPK st v pid pk
  peerCanSign-Msb4 {pid} {st = st} r stP pcsv pkH sig msv = {!!}
 
  peerCanSignEp≡ : ∀ {pid v v' pk s'}
                   → PeerCanSignForPK s' v pid pk
                   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                   → PeerCanSignForPK s' v' pid pk
  peerCanSignEp≡ (mkPCS4PK 𝓔₁ 𝓔id≡₁ 𝓔inSys₁ mbr₁ nid≡₁ pk≡₁) refl = (mkPCS4PK 𝓔₁ 𝓔id≡₁ 𝓔inSys₁ mbr₁ nid≡₁ pk≡₁)


  peerCanSignPK-PostSt :  ∀ {pid pid' s' outs pk v}{st : SystemState}
                       → ReachableSystemState st
                       → (stP : StepPeer st pid s' outs)
                       → Meta-Honest-PK pk
                       → PeerCanSignForPK (peerStates st pid') v pid' pk
                       → PeerCanSignForPK (peerStates (StepPeer-post stP) pid') v pid' pk

  -- This property does not hold!  The problem is that there is nothing constraining peerStates st
  -- pid': pid' might be uninitialised, in which case PeerCanSignForPK (peerStates st pid') v' pid'
  -- pk does not tell us anything. We cannot add a hypothesis that initialised st pid' ≡ initd,
  -- because that's what we're trying to prove in one of the places this is used (note that pid in
  -- msg∈pool⇒initd corresponds to pid' here).

  -- I think we are running into exactly the thing that unwind helps with: it takes us back to the
  -- the transition that first sends a signature, where we know it hasn't been sent before, and must be
  -- sent my a step-msg, which only occurs if the sender is initialised, which we then carry forward
  -- (see carrInit in Yasm.Properties).  That's not to say we can't succeed without unwind, of course,
  -- but this challenge highlights the difference well.

  peerCanSignPK-Inj :  ∀ {pid pid' s' outs pk v v'}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                    → Meta-Honest-PK pk
                    → PeerCanSignForPK st v' pid' pk
                    → PeerCanSignForPK (StepPeer-post (step-honest stP)) v pid pk
                    → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                    → pid ≡ pid'
  peerCanSignPK-Inj {pid} {pid'} {v = v} r stP pkH pcsv'Pre pcsvPost refl
    with pid ≟ pid'
  ...| yes refl = refl
  ...| no pids≢
     with step-peer (step-honest stP)
  ...| theStep
     with PeerCanSignForPK-stable r theStep pcsv'Pre
  ...| pcsv'Post
     with availEpochsConsistent (step-s r theStep) pcsv'Post pcsvPost
  ...| refl = ⊥-elim (pids≢ (NodeId-PK-OK-injective (𝓔 pcsvPost)
                                                    (PCS4PK⇒NodeId-PK-OK pcsvPost)
                                                    ( PCS4PK⇒NodeId-PK-OK pcsv'Post)))

  msg∈pool⇒initd : ∀ {pid pk v}{st : SystemState}
                   → ReachableSystemState st
                   → PeerCanSignForPK st v pid pk
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                   → initialised st pid ≡ initd
  msg∈pool⇒initd {pid'} {st = st} step@(step-s r (step-peer {pid} (step-honest stPeer))) pcs pkH sig msv
    with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₁ (m∈outs , pcsN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr st step hb)
  ...| inj₂ refl
    with stPeer
  ...| step-msg _ initP
    with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj r stPeer pkH {! pcs !} {! pcsN !} refl))
  msg∈pool⇒initd {pid'} {st = st} step@(step-s r (step-peer {pid} (step-honest stPeer))) pcs pkH sig msv
     | inj₂ msb4 rewrite msgSameSig msv
       with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = msg∈pool⇒initd r {! pcs !} pkH sig msb4
  msg∈pool⇒initd {pid'} (step-s r (step-peer {pid} cheat@(step-cheat c))) pcs pkH sig msv
    with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid} {pid'} cheat unit
       = peersRemainInitialized (step-peer cheat) (msg∈pool⇒initd r {! pcs !} pkH sig msb4)


  -- This proof holds for now because there is no epoch changes yet
  -- TODO: generalize it to prove it even when there is epoch changes
  noEpochChange : ∀ {pid s' outs}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                    → initialised st pid ≡ initd
                    → (₋rmamEC (peerStates st pid)) ^∙ rmEpoch ≡ (₋rmamEC s') ^∙ rmEpoch
  noEpochChange _ (step-init uninit) initP = let uninit≡init = trans (sym uninit) initP
                                             in contradiction uninit≡init λ {()}
  noEpochChange _ (step-msg {nm} _ _) _
    with nm
  ... | _ , P m = refl
  ... | _ , V m = refl
  ... | _ , C m = refl
  -- NOTE: this property isn't used (yet?).  It is proved except for one hole, where we know that PCS4PK
  -- holds in the post-state, but we need to know it holds in the prestate.  But this might not be true
  -- if stP is step-init and establishes PCS4PK.  Given that we're not using this yet, I suggest we
  -- leave this for now and concentrate on proving the properties we need in the short term.  (My
  -- understanding is that this property is intended as something that will hold more generally when
  -- we do implement epoch changes.)


  noEpochChangeYet : ∀ {pid s' outs v pk}{st : SystemState}
                     → ReachableSystemState st
                     → (stP : StepPeer st pid s' outs)
                     → PeerCanSignForPK (StepPeer-post stP) v pid pk
                     → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                     → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                     → (₋rmEC s') ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                     → (₋rmEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
  noEpochChangeYet r (step-honest (step-init uni)) pcsv pkH sig msv eid≡ = ⊥-elim (uninitd≢initd (trans (sym uni) (msg∈pool⇒initd r {! pcsv!} pkH sig msv)))
  noEpochChangeYet {pid} {v = v} {st = st} r (step-honest sm@(step-msg  _ ini)) pcsv pkH sig msv eid≡ rewrite noEpochIdChangeYet r refl sm ini = eid≡
  noEpochChangeYet {pid'} r cheat@(step-cheat {pid} c) pcsv pkH sig msv eid≡ = eid≡

  oldVoteRound≤lvr :  ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   → initialised pre pid ≡ initd
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK pre v pid pk
                   → (₋rmEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid'} {pre = pre} (step-s {pre = prev} r (step-peer {pid = pid} cheat@(step-cheat c)))
                    initP pkH sig msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = oldVoteRound≤lvr r (trans (sym (overrideSameVal-correct pid pid')) initP) pkH sig msb4 vspk eid≡
       = oldVoteRound≤lvr r pkH sig msb4 {! vspk !} eid≡
  oldVoteRound≤lvr {pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid} stepPeer@(step-honest stPeer)))
                   initP pkH sig msv vspk eid≡
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with pid ≟ pid'
  ...| no  pid≢ = oldVoteRound≤lvr r pkH sig msb4 {! vspk !} eid≡
  ...| yes refl = let  -- pcs = peerCanSignSameS vspk (sym (StepPeer-post-lemma stepPeer))
                       canSign = peerCanSign-Msb4 r stepPeer {!!} pkH sig msb4
                       initP = msg∈pool⇒initd r canSign pkH sig msb4
                       ep≡   = noEpochIdChangeYet r refl stPeer initP
                       lvr≤  = lastVoteRound-mono r refl stPeer initP ep≡
                   in ≤-trans (oldVoteRound≤lvr r initP pkH sig msb4 canSign (trans ep≡ eid≡)) lvr≤
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid} {st'} stepPeer@(step-honest stPeer)))
                   initP pkH sig msv vspk eid≡
     | inj₁ (m∈outs , vspkN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with pid ≟ pid'
  ...| yes refl = ≡⇒≤ (newVoteEpoch≡⇒GreaterRound r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV (sym eid≡))
  ...| no  pid≢ = ?
{-
    with stPeer
  ... | step-msg _ pidIn
     with availEpochsConsistent r (inPre initP vspk) (inPost pidIn stPeer vspkN)
  ... | refl = ⊥-elim (pid≢ (NodeId-PK-OK-injective (𝓔 vspkN)
                                                    (PCS4PK⇒NodeId-PK-OK vspkN)
                                                    (PCS4PK⇒NodeId-PK-OK vspk)))
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj r stPeer pkH {! vspk !} vspkN refl))
-}


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r step@(step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' eid≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
                     --pcsv'  = peerCanSignSameS vspkv' (sym (StepPeer-post-lemma (step-honest step)))
                     vspkv' = peerCanSign-Msb4 r (step-honest step) {! pcsv' !} pkH sv' m'mwsb
                     rv'<rv = oldVoteRound≤lvr r psI pkH sv' m'mwsb vspkv' eid≡
                 in ⊥-elim (<⇒≢ (s≤s rv'<rv) (sym r≡))
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
       = ⊥-elim (¬msb (qcVotesSentB4 r psI refl qc∈m refl vs∈qc))

  votesOnce₂ : VO.ImplObligation₂
  votesOnce₂ {pk = pk} {st} r (step-msg {_ , P m} _ psI) hpk v⊂m m∈outs sig vnew
             vpk v'⊂m' m'∈outs sig' v'new vpk' es≡ rnds≡
     with m∈outs | m'∈outs
  ...| here refl | here refl
     with v⊂m                          | v'⊂m'
  ...| vote∈vm                         | vote∈vm = refl
  ...| vote∈vm                         | vote∈qc vs∈qc' v≈rbld' (inV qc∈m')
       rewrite cong ₋vSignature v≈rbld'
       = ⊥-elim (v'new (qcVotesSentB4 r psI refl qc∈m' refl vs∈qc'))
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) | _
       rewrite cong ₋vSignature v≈rbld
       = ⊥-elim (vnew (qcVotesSentB4 r psI refl qc∈m refl vs∈qc))
