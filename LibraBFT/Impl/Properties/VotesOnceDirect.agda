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
open import LibraBFT.Impl.Handle.Properties sha256 sha256-cr
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
 {- newVoteEpoch≡⇒GreaterRound _ (step-init _) v⊂m m∈outs sig = ⊥-elim (¬Any[] m∈outs)
  newVoteEpoch≡⇒GreaterRound {pre = pre} {pid} {m = m} r (step-msg {_ , P pm} _ pinit)
                                 v⊂m (here refl) sig vnew ep≡
     with v⊂m
  ...| vote∈vm = refl
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
       = ⊥-elim (vnew (qcVotesSentB4 r pinit refl qc∈m refl vs∈qc))-}


  -- TODO-2 : This became obsolete, but is restored here as it is used below.  It should go
  -- somewhere else.  Handle.Properties?
  noEpochChangeYet : ∀ {pid s' outs v pk}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                    → PeerCanSignForPK s' v pid pk
                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                    → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                    → (₋rmamEC s') ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                    → (₋rmamEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)


  peerCanSign-Ep≡ : ∀ {pid s' outs v v' pk}{st : SystemState}
                    → ReachableSystemState st
                    → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                    → PeerCanSignForPK s' v pid pk
                    → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                    → PeerCanSignForPK s' v' pid pk

  peerCanSignPreSt : ∀ {pid s' outs v pk}{st : SystemState}
                     → ReachableSystemState st
                     → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                     → PeerCanSignForPK s' v pid pk
                     → (₋rmamEC (peerStates st pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                     → PeerCanSignForPK (peerStates st pid) v pid pk

  msg∈pool⇒initd : ∀ {pid s' outs pk v}{st : SystemState}
                   → (r : ReachableSystemState st)
                   → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                   → PeerCanSignForPK s' v pid pk
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
                   → initialised st pid ≡ initd


  signPK-Inj :  ∀ {pid pid' s' outs pk v v'}{st : SystemState}
                → ReachableSystemState st
                → (stP : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
                → Meta-Honest-PK pk
                → PeerCanSignForPK (peerStates st pid') v' pid' pk
                → PeerCanSignForPK s' v pid pk
                → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                → pid ≡ pid'


  oldVoteRound≤lvr :  ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   -- → initialised pre pid ≡ initd
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK (peerStates pre pid) v pid pk
                   → (₋rmamEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmamEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid = pid'} {pre = pre} (step-s {pre = prev} r (step-peer {pid = pid} cheat@(step-cheat c)))
                    pkH sig msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = oldVoteRound≤lvr r pkH sig msb4 vspk eid≡
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid = pid} (step-honest stPeer)))
                   pkH sig msv vspk eid≡
     with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with pid ≟ pid'
  ...| no  pid≢ = oldVoteRound≤lvr r pkH sig msb4 vspk eid≡
  ...| yes refl = let  ep≡   = noEpochChangeYet r stPeer vspk pkH sig msb4 eid≡
                       initP = msg∈pool⇒initd r stPeer vspk pkH sig msb4
                       lvr≤  = lastVoteRound-mono r refl stPeer initP (trans ep≡ (sym eid≡))
                       canSign = peerCanSignPreSt r stPeer vspk ep≡
                   in ≤-trans (oldVoteRound≤lvr r pkH sig msb4 canSign ep≡) lvr≤

  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s {pre = prev} r stepPeer@(step-peer {pid} {st'} (step-honest stPeer)))
                   pkH sig msv vspk eid≡
     | inj₁ (m∈outs , vspkN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with pid ≟ pid'
  ...| yes refl = ≡⇒≤ (newVoteEpoch≡⇒GreaterRound r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV (sym eid≡))
  ...| no  pid≢ = ⊥-elim (pid≢ (signPK-Inj r stPeer pkH vspk vspkN refl))


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r step@(step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' eid≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = peerCanSignPreSt r step (peerCanSign-Ep≡ r step vspkv eid≡) eid≡
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
