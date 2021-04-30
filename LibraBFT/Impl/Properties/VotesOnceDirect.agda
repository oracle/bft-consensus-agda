{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module proves the two "VotesOnce" proof obligations for our fake handler


-- Note that the proofs in this file were broken by the changes to eliminate EpochConfigs from the
-- system model and to move towards more realistic initialisation.  Below some parts of the proofs
-- are commented out and some holes are left to enable exploring where the proof breaks down.

-- One key issue is that, with the new system model, whether a peer can sign a message for a PK in a
-- particular epoch is a function of its peer state (which now includes the EpochConfigs it knows
-- about), rather than a function of the available EpochConfigs in the system state as it was
-- before.  This means that a peer can learn of a new EpochConfig during a step (either from
-- GenesisInfo in step-init or, eventually, by committing an epoch-changing transaction and adding
-- another EpochConfig as a result).  Thus, unlike before, it is possible for a peer step to sign
-- and send a new message, even though PeerCanSignForPK did not hold in its prestate.  For that
-- reason, the ImplObligation₁ now receives evidence that it can sign in the step's post state (in
-- the form of PeerCanSignForPK s' v pid pk), whereas previously, it received evidence that it could
-- do so in the step's prestate (in the form of ValidSenderForPK (availEpochs pre) v pid pk).  I
-- think we will need to reason about step-init and step-msg separately.
--
-- For step-init, we can aim for a contradiction to the hypothesis that there is a message (m')
-- previously sent signed for the same PK and for the same epoch as v.  Because uninitialised peers
-- don't send messages, and once initialised, a peer remains initialised, and because (by PK-inj)
-- there is only one peer that can legitimately sign for that epoch and PK, v' must not have been
-- sent before.  However, this is complicated by the possibility of hash collisions, because we only
-- infer that a vote with the same signature is for the same epoch indirectly via hashes
-- (sameHonestSig⇒sameVoteData).
--
-- For step-msg, at least for our current simplified "implementation" we do not change epochs, so if
-- it was PeerCanSignForPK st' v pid pk holds, then PeerCanSignForPK (peerStates pre pid) v pid pk
-- held, so we can perhaps continue with something like the previous proof approach for this case.
-- But there are other wrinkles, such as the fact that EpochConfigs are now in peer states, not
-- system state, so we need to know that EpochConfigs for the same epoch in two (potentially)
-- difference peer states are the same; this is true for now because only one EpochConfig derived
-- from GenesisInfo upon initialisation is the same for everyone; later we will need to use the fact
-- that commits are consistent to show that subsequent EpochConfigs added by epoch changes are also
-- consistent.  For now we have a postulate availEpochsConsistent for this purpose, and a new
-- PK-inj-same-ECs which allows is to use PK-inj to determine that two peers are the same given that
-- we know their EpochConfigs are consistent.  See the unwind-based proof in VotesOnce, which is
-- complete and uses these.

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
open import LibraBFT.Yasm.Yasm ℓ-RoundManagerAndMeta ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open import LibraBFT.Abstract.Util.AvailableEpochs NodeId ℓ-EC EpochConfig EpochConfig.epochId
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
                               → v ^∙ vEpoch ≡ (₋rmamEC s') ^∙ rmEpoch
                               → v ^∙ vRound ≡ (₋rmamEC s') ^∙ rmLastVotedRound
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


  peerCanSign-Msb4 : ∀ {pid v s' outs pk}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeer st pid s' outs)
                    → PeerCanSignForPK (peerStates (StepPeer-post stP) pid) v pid pk
                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                    → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                    → PeerCanSignForPK (peerStates st pid) v pid pk
  peerCanSign-Msb4 {pid} {st = st} r stP pcsv pkH sig msv
    = let rnam≡ = PeerCanSignForPKBogus1 {peerStates (StepPeer-post stP) pid} {peerStates st pid}
          acEp≡ = PeerCanSignForPKBogus2 {peerStates (StepPeer-post stP) pid} {peerStates st pid} rnam≡
      in PeerCanSignForPKAux pcsv rnam≡ acEp≡

  peerCanSignEp≡ : ∀ {pid v v' pk s'}
                   → PeerCanSignForPK s' v pid pk
                   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                   → PeerCanSignForPK s' v' pid pk
  peerCanSignEp≡ pcsv refl = mkPCS4PK (eInRange pcsv) (𝓔 pcsv) (𝓔≡ pcsv) (mbr pcsv) (nid≡ pcsv) (pk≡ pcsv)

  peerCanSignPK-Inj :  ∀ {pid pid' s' outs pk v v'}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                    → Meta-Honest-PK pk
                    → PeerCanSignForPK (peerStates st pid') v' pid' pk
                    → PeerCanSignForPK s' v pid pk
                    → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                    → pid ≡ pid'
  peerCanSignPK-Inj {pid} {pid'} {v = v} r stP pkH pcsv'Pre pcsvPost refl
    with pid ≟ pid'
  ...| yes refl = refl
  ...| no pids≢ = ⊥-elim (pids≢ (PK-inj-same-ECs {!!} (trans (pk≡ pcsv'Pre) (sym (pk≡ pcsvPost)))))


  msg∈pool⇒initd : ∀ {pid pk v}{st : SystemState}
                   → ReachableSystemState st
                   → PeerCanSignForPK (peerStates st pid) v pid pk
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
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj r stPeer pkH pcs pcsN refl))
  msg∈pool⇒initd {pid'} {st = st} step@(step-s r (step-peer {pid} (step-honest stPeer))) pcs pkH sig msv
     | inj₂ msb4 rewrite msgSameSig msv
       with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = msg∈pool⇒initd r pcs pkH sig msb4
  msg∈pool⇒initd {pid'} (step-s r (step-peer {pid} cheat@(step-cheat c))) pcs pkH sig msv
    with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid} {pid'} cheat unit
       = peersRemainInitialized (step-peer cheat) (msg∈pool⇒initd r pcs pkH sig msb4)

  -- NOTE: this property isn't used (yet?).  It is proved except for one hole, where we know that PCS4PK
  -- holds in the post-state, but we need to know it holds in the prestate.  But this might not be true
  -- if stP is step-init and establishes PCS4PK.  Given that we're not using this yet, I suggest we
  -- leave this for now and concentrate on proving the properties we need in the short term.  (My
  -- understanding is that this property is intended as something that will hold more generally when
  -- we do implement epoch changes.)
  noEpochChangeYet : ∀ {pid s' outs v pk}{st : SystemState}
                     → ReachableSystemState st
                     → (stP : StepPeer st pid s' outs)
                     → PeerCanSignForPK (peerStates (StepPeer-post stP) pid) v pid pk
                     → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                     → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                     → (₋rmamEC s') ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                     → (₋rmamEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
  noEpochChangeYet r (step-honest (step-init uni)) pcsv pkH sig msv eid≡ = ⊥-elim (uninitd≢initd (trans (sym uni) (msg∈pool⇒initd r {! pcsv!} pkH sig msv)))
  noEpochChangeYet {pid} {v = v} {st = st} r (step-honest sm@(step-msg  _ ini)) pcsv pkH sig msv eid≡ rewrite noEpochIdChangeYet r refl sm ini = eid≡
  noEpochChangeYet {pid'} r cheat@(step-cheat {pid} c) pcsv pkH sig msv eid≡
                     rewrite sym (cheatStepDNMPeerStates₁ {pid} {pid'} cheat unit) = eid≡

  oldVoteRound≤lvr :  ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK (peerStates pre pid) v pid pk
                   → (₋rmamEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmamEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid'} {pre = pre} (step-s {pre = prev} r (step-peer {pid = pid} cheat@(step-cheat c)))
                    pkH sig msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = oldVoteRound≤lvr r pkH sig msb4 vspk eid≡
  oldVoteRound≤lvr {pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid} stepPeer@(step-honest stPeer)))
                   pkH sig msv vspk eid≡
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with pid ≟ pid'
  ...| no  pid≢ = oldVoteRound≤lvr r pkH sig msb4 vspk eid≡
  ...| yes refl = let  pcs = peerCanSignSameS vspk (sym (StepPeer-post-lemma stepPeer))
                       canSign = peerCanSign-Msb4 r stepPeer pcs pkH sig msb4
                       initP = msg∈pool⇒initd r canSign pkH sig msb4
                       ep≡   = noEpochIdChangeYet r refl stPeer initP
                       lvr≤  = lastVoteRound-mono r refl stPeer initP ep≡
                   in ≤-trans (oldVoteRound≤lvr r pkH sig msb4 canSign (trans ep≡ eid≡)) lvr≤
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid} {st'} stepPeer@(step-honest stPeer)))
                   pkH sig msv vspk eid≡
     | inj₁ (m∈outs , vspkN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with pid ≟ pid'
  ...| yes refl = ≡⇒≤ (newVoteEpoch≡⇒GreaterRound r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV (sym eid≡))
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj r stPeer pkH vspk vspkN refl))


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r step@(step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' eid≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
                     pcsv'  = peerCanSignSameS vspkv' (sym (StepPeer-post-lemma (step-honest step)))
                     vspkv' = peerCanSign-Msb4 r (step-honest step) pcsv' pkH sv' m'mwsb
                     rv'<rv = oldVoteRound≤lvr r pkH sv' m'mwsb vspkv' eid≡
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
