{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.Impl.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState. 

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
open import LibraBFT.Yasm.Types
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


  newVoteEpoch≡⇒Round≡ : ∀ {st : SystemState}{pid s' outs v m pk}
                               → ReachableSystemState st
                               → StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs)
                               → v  ⊂Msg m → send m ∈ outs → (sig : WithVerSig pk v)
                               → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                               → v ^∙ vEpoch ≡ (₋rmEC s') ^∙ rmEpoch
                               → v ^∙ vRound ≡ (₋rmEC s') ^∙ rmLastVotedRound
  newVoteEpoch≡⇒Round≡ r (step-msg {_ , P pm} _ pinit) v⊂m (here refl) sig vnew ep≡
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

  peerCanSignEp≡ : ∀ {pid v v' pk s'}
                   → PeerCanSignForPK s' v pid pk
                   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                   → PeerCanSignForPK s' v' pid pk
  peerCanSignEp≡ (mkPCS4PK 𝓔₁ 𝓔id≡₁ 𝓔inSys₁ mbr₁ nid≡₁ pk≡₁) refl
    = (mkPCS4PK 𝓔₁ 𝓔id≡₁ 𝓔inSys₁ mbr₁ nid≡₁ pk≡₁)

  MsgWithSig⇒ValidSenderInitialised :
     ∀ {st v pk}
     → ReachableSystemState st
     → Meta-Honest-PK pk → (sig : WithVerSig pk v)
     → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     → ∃[ pid ] ( initialised st pid ≡ initd
                × PeerCanSignForPK st v pid pk )
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer (step-honest {pid} stP))) pkH sig msv
     with newMsg⊎msgSentB4 r stP pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ (newV , m∈outs , pcsN)
     with stP
  ...| step-msg _ initP
      with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb   = ⊥-elim (PerState.meta-sha256-cr st (step-s r step) hb)
  ...| inj₂ refl = pid , peersRemainInitialized step initP , peerCanSignEp≡ pcsN refl
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer (step-honest stP))) pkH sig msv
     | inj₁ msb4 rewrite msgSameSig msv
     with MsgWithSig⇒ValidSenderInitialised {v = v} r pkH sig msb4
  ...| pid , initP , pcsPre = pid ,
                              peersRemainInitialized step initP ,
                              PeerCanSignForPK-stable r step pcsPre
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer cheat@(step-cheat x))) pkH sig msv
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     with MsgWithSig⇒ValidSenderInitialised {v = v} r pkH sig msb4
  ...| pid , initP , pcsPre = pid ,
                              peersRemainInitialized step initP ,
                              PeerCanSignForPK-stable r step pcsPre


  peerCanSign-Msb4 : ∀ {pid v pk}{pre post : SystemState}
                    → ReachableSystemState pre
                    → Step pre post
                    → PeerCanSignForPK post v pid pk
                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                    → PeerCanSignForPK pre v pid pk
  peerCanSign-Msb4 r step (mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁) pkH sig msv
    = mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁

  peerCanSignPK-Inj :  ∀ {pid pid' pk v v'}{st : SystemState}
                    → ReachableSystemState st
                    → Meta-Honest-PK pk
                    → PeerCanSignForPK st v' pid' pk
                    → PeerCanSignForPK st v pid pk
                    → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                    → pid ≡ pid'
  peerCanSignPK-Inj {pid} {pid'} r pkH pcs' pcs eid≡
     with availEpochsConsistent r pcs' pcs
  ...| refl
     with NodeId-PK-OK-injective (𝓔 pcs) (PCS4PK⇒NodeId-PK-OK pcs) (PCS4PK⇒NodeId-PK-OK pcs')
  ...| pids≡ = pids≡


  msg∈pool⇒initd : ∀ {pid pk v}{st : SystemState}
                   → ReachableSystemState st
                   → PeerCanSignForPK st v pid pk
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                   → initialised st pid ≡ initd
  msg∈pool⇒initd {pid'} {st = st} step@(step-s r (step-peer {pid} (step-honest stPeer))) pcs pkH sig msv
    with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ (newV , m∈outs , pcsN)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr st step hb)
  ...| inj₂ refl
    with stPeer
  ...| step-msg _ initP
    with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj step pkH pcs pcsN refl))
  msg∈pool⇒initd {pid'} (step-s r step@(step-peer {pid} (step-honest stPeer))) pcs pkH sig msv
     | inj₁ msb4 rewrite msgSameSig msv
       with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = let pcsmsb4 = peerCanSign-Msb4 r step pcs pkH sig msb4
                  in msg∈pool⇒initd r pcsmsb4 pkH sig msb4
  msg∈pool⇒initd {pid'} (step-s r step@(step-peer {pid} cheat@(step-cheat c))) pcs pkH sig msv
    with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
       = let pcsmsb4 = peerCanSign-Msb4 r step pcs pkH sig msb4
             initPre = msg∈pool⇒initd r pcsmsb4  pkH sig msb4
         in peersRemainInitialized (step-peer cheat) initPre


  noEpochChangeYet : ∀ {pid s' outs v pk}{st : SystemState}
                     → ReachableSystemState st
                     → (stP : StepPeer st pid s' outs)
                     → PeerCanSignForPK (StepPeer-post stP) v pid pk
                     → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                     → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                     → (₋rmEC s') ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                     → (₋rmEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
  noEpochChangeYet r step@(step-honest (step-init uni)) pcsv pkH sig msv eid≡
    = let pcsPre = peerCanSign-Msb4 r (step-peer step) pcsv pkH sig msv
      in ⊥-elim (uninitd≢initd (trans (sym uni) (msg∈pool⇒initd r pcsPre pkH sig msv)))
  noEpochChangeYet r (step-honest sm@(step-msg  _ ini)) pcsv pkH sig msv eid≡
    rewrite noEpochIdChangeYet r refl sm ini = eid≡
  noEpochChangeYet r cheat@(step-cheat c) pcsv pkH sig msv eid≡ = eid≡


  oldVoteRound≤lvr :  ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK pre v pid pk
                   → (₋rmEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid'} (step-s r step@(step-peer {pid = pid} cheat@(step-cheat c)))
                   pkH sig msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = let pcsmsb4 = peerCanSign-Msb4 r step vspk pkH sig msb4
         in oldVoteRound≤lvr r pkH sig msb4 pcsmsb4 eid≡
  oldVoteRound≤lvr {pid'} step@(step-s r stP@(step-peer {pid} (step-honest stPeer)))
                   pkH sig msv vspk eid≡
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₁ msb4 rewrite msgSameSig msv
     with peerCanSign-Msb4 r stP vspk pkH sig msb4
  ...| pcsmsb4
     with pid ≟ pid'
  ...| no  pid≢ = oldVoteRound≤lvr r  pkH sig msb4 pcsmsb4 eid≡
  ...| yes refl = let  initP = msg∈pool⇒initd r pcsmsb4 pkH sig msb4
                       ep≡   = noEpochIdChangeYet r refl stPeer initP
                       lvr≤  = lastVoteRound-mono r refl stPeer initP ep≡
                   in ≤-trans (oldVoteRound≤lvr r pkH sig msb4 pcsmsb4 (trans ep≡ eid≡)) lvr≤
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s r (step-peer {pid} {st'} stepPeer@(step-honest stPeer)))
                   pkH sig msv vspk eid≡
     | inj₂ (newV , m∈outs , vspkN)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with pid ≟ pid'
  ...| yes refl = ≡⇒≤ (newVoteEpoch≡⇒Round≡ r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV (sym eid≡))
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj step pkH vspk vspkN refl))


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r stMsg@(step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' eid≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
                     step   = step-peer (step-honest stMsg)
                     vspre' = peerCanSign-Msb4 r step vspkv' pkH sv' m'mwsb
                     rv'<rv = oldVoteRound≤lvr r pkH sv' m'mwsb vspre' eid≡
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
