{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS

import      LibraBFT.Concrete.Properties.VotesOnce as VO

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp
open import LibraBFT.Impl.Properties.VotesOnce

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.Impl.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState.

module LibraBFT.Impl.Properties.VotesOnceDirect where


  newVoteEpoch≡⇒Round≡ : ∀ {st : SystemState}{pid s' outs v m pk}
                       → ReachableSystemState st
                       → StepPeerState pid (msgPool st) (initialised st)
                                       (peerStates st pid) (s' , outs)
                       → v ⊂Msg m → send m ∈ outs → (sig : WithVerSig pk v)
                       → Meta-Honest-PK pk → ¬ (∈GenInfo (ver-signature sig))
                       → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                       → v ^∙ vEpoch ≡ (₋rmEC s') ^∙ rmEpoch
                       → v ^∙ vRound ≡ (₋rmEC s') ^∙ rmLastVotedRound
  newVoteEpoch≡⇒Round≡ r step@(step-msg {_ , P pm} _ pinit) v⊂m (here refl)
                       sig pkH ¬gen vnew ep≡
     with v⊂m
  ...| vote∈vm = refl
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
       = let qc∈rm = VoteMsgQCsFromRoundManager r step pkH v⊂m (here refl) qc∈m
         in ⊥-elim (vnew (qcVotesSentB4 r pinit qc∈rm vs∈qc ¬gen))

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

  MsgWithSig⇒ValidSenderInitialised : ∀ {st v pk}
                                    → ReachableSystemState st
                                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                                    → ¬ (∈GenInfo (ver-signature sig))
                                    → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                                    → ∃[ pid ] ( initialised st pid ≡ initd
                                               × PeerCanSignForPK st v pid pk )
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer (step-honest {pid} stP))) pkH sig ¬gen msv
     with msgSameSig msv
  ...| refl
     with newMsg⊎msgSentB4 r stP pkH (msgSigned msv) ¬gen (msg⊆ msv) (msg∈pool msv)
  ...| inj₁ (m∈outs , pcsN , newV)
     with stP
  ...| step-msg _ initP
      with PerState.sameSig⇒sameVoteDataNoCol st (step-s r step) (msgSigned msv) sig (msgSameSig msv)
  ...| refl = pid , peersRemainInitialized step initP , peerCanSignEp≡ pcsN refl
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer (step-honest stP))) pkH sig ¬gen msv
     | refl
     | inj₂ msb4
     with MsgWithSig⇒ValidSenderInitialised {v = v} r pkH sig ¬gen msb4
  ...| pid , initP , pcsPre = pid ,
                              peersRemainInitialized step initP ,
                              PeerCanSignForPK-stable r step pcsPre
  MsgWithSig⇒ValidSenderInitialised {st} {v} (step-s r step@(step-peer cheat@(step-cheat x))) pkH sig ¬gen msv
     with msgSameSig msv
  ...| refl
     with ¬cheatForgeNew cheat refl unit pkH msv ¬gen
  ...| msb4
     with MsgWithSig⇒ValidSenderInitialised {v = v} r pkH sig ¬gen msb4
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
  ...| refl = refl


  msg∈pool⇒initd : ∀ {pid pk v}{st : SystemState}
                 → ReachableSystemState st
                 → PeerCanSignForPK st v pid pk
                 → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                 → ¬ (∈GenInfo (ver-signature sig))
                 → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                 → initialised st pid ≡ initd
  msg∈pool⇒initd {pid'} {st = st} step@(step-s r (step-peer {pid} (step-honest stPeer))) pcs pkH sig ¬gen msv
     with msgSameSig msv
  ...| refl
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) ¬gen (msg⊆ msv) (msg∈pool msv)
  ...| inj₁ (m∈outs , pcsN , newV)
     with sameSig⇒sameVoteData (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr st step hb)
  ...| inj₂ refl
     with stPeer
  ...| step-msg _ initP
     with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj step pkH pcs pcsN refl))
  msg∈pool⇒initd {pid'} (step-s r step@(step-peer {pid} (step-honest stPeer))) pcs pkH sig ¬gen msv
     | refl
     | inj₂ msb4
     with pid ≟ pid'
  ...| yes refl = refl
  ...| no  pid≢ = let pcsmsb4 = peerCanSign-Msb4 r step pcs pkH sig msb4
                  in msg∈pool⇒initd r pcsmsb4 pkH sig ¬gen msb4
  msg∈pool⇒initd {pid'} (step-s r step@(step-peer {pid} cheat@(step-cheat c))) pcs pkH sig ¬gen msv
     with msgSameSig msv
  ...| refl
     with ¬cheatForgeNew cheat refl unit pkH msv ¬gen
  ...| msb4
       = let pcsmsb4 = peerCanSign-Msb4 r step pcs pkH sig msb4
             initPre = msg∈pool⇒initd r pcsmsb4  pkH sig ¬gen msb4
         in peersRemainInitialized (step-peer cheat) initPre


  noEpochChange : ∀ {pid s' outs v pk}{st : SystemState}
                → ReachableSystemState st
                → (stP : StepPeerState pid (msgPool st) (initialised st)
                                       (peerStates st pid) (s' , outs))
                → PeerCanSignForPK st v pid pk
                → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                → ¬ ∈GenInfo (ver-signature sig)
                → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                → (₋rmEC s') ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                → (₋rmEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
  noEpochChange r (step-init uni) pcs pkH sig ∉gen msv eid≡
    = ⊥-elim (uninitd≢initd (trans (sym uni) (msg∈pool⇒initd r pcs pkH sig ∉gen msv)))
  noEpochChange r sm@(step-msg _ ini) pcs pkH sig ∉gen msv eid≡
    rewrite noEpochIdChangeYet r refl sm ini = eid≡

  oldVoteRound≤lvr : ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → ¬ (∈GenInfo (ver-signature sig))
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK pre v pid pk
                   → (₋rmEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid'} (step-s r step@(step-peer {pid = pid} cheat@(step-cheat c)))
                   pkH sig ¬gen msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv (¬subst ¬gen (msgSameSig msv))
  ...| msb4 rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = let pcsmsb4 = peerCanSign-Msb4 r step vspk pkH sig msb4
         in oldVoteRound≤lvr r pkH sig ¬gen msb4 pcsmsb4 eid≡
  oldVoteRound≤lvr {pid'} step@(step-s r stP@(step-peer {pid} (step-honest stPeer)))
                   pkH sig ¬gen msv vspk eid≡
     with msgSameSig msv
  ...| refl
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) ¬gen (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with peerCanSign-Msb4 r stP vspk pkH sig msb4
  ...| pcsmsb4
     with pid ≟ pid'
  ...| no  pid≢ = oldVoteRound≤lvr r  pkH sig ¬gen msb4 pcsmsb4 eid≡
  ...| yes refl = let  initP = msg∈pool⇒initd r pcsmsb4 pkH sig ¬gen msb4
                       ep≡   = noEpochChange r stPeer pcsmsb4 pkH sig ¬gen msb4 eid≡
                       lvr≤  = lastVoteRound-mono r refl stPeer initP (trans ep≡ (sym eid≡))
                   in ≤-trans (oldVoteRound≤lvr r pkH sig ¬gen msb4 pcsmsb4 ep≡) lvr≤
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s r (step-peer {pid} (step-honest stPeer)))
                   pkH sig ¬gen msv vspk eid≡
     | refl
     | inj₁ (m∈outs , vspkN , newV)
     with sameSig⇒sameVoteData (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with pid ≟ pid'
  ...| yes refl = ≡⇒≤ (newVoteEpoch≡⇒Round≡ r stPeer (msg⊆ msv) m∈outs (msgSigned msv)
                                            pkH ¬gen newV (sym eid≡))
  ...| no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj step pkH vspk vspkN refl))


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r stMsg@(step-msg {_ , P m} m∈pool psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬gen ¬msb vspkv v'⊂m' m'∈pool sv' ¬gen' eid≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
                     step   = step-peer (step-honest stMsg)
                     vspre' = peerCanSign-Msb4 r step vspkv' pkH sv' m'mwsb
                     rv'<rv = oldVoteRound≤lvr r pkH sv' ¬gen' m'mwsb vspre' eid≡
                 in ⊥-elim (<⇒≢ (s≤s rv'<rv) (sym r≡))
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
     = let qc∈rm = VoteMsgQCsFromRoundManager r stMsg pkH v⊂m (here refl) qc∈m
       in ⊥-elim (¬msb (qcVotesSentB4 r psI qc∈rm vs∈qc ¬gen))

  votesOnce₂ : VO.ImplObligation₂
  votesOnce₂ {pk = pk} {st} r stMsg@(step-msg {_ , P m} m∈pool psI) pkH v⊂m m∈outs sig ¬gen vnew
             vpk v'⊂m' m'∈outs sig' ¬gen' v'new vpk' es≡ rnds≡
     with m∈outs | m'∈outs
  ...| here refl | here refl
     with v⊂m                          | v'⊂m'
  ...| vote∈vm                         | vote∈vm = refl
  ...| vote∈vm                         | vote∈qc vs∈qc' v≈rbld' (inV qc∈m')
       rewrite cong ₋vSignature v≈rbld'
       = let qc∈rm' = VoteMsgQCsFromRoundManager r stMsg pkH v'⊂m' (here refl) qc∈m'
         in ⊥-elim (v'new (qcVotesSentB4 r psI qc∈rm' vs∈qc' ¬gen'))
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) | _
       rewrite cong ₋vSignature v≈rbld
       = let qc∈rm = VoteMsgQCsFromRoundManager r stMsg pkH v⊂m (here refl) qc∈m
         in ⊥-elim (vnew (qcVotesSentB4 r psI qc∈rm vs∈qc ¬gen))
