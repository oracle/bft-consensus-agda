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

  -- TODO-2 : This became obsolete, but is restored here as it is used below.  It should go
  -- somewhere else.  Handle.Properties?
  noEpochChangeYet : ∀ {pre : SystemState}{pid}{initd' ppre ppost msgs}
                   → ReachableSystemState pre
                   → ppre ≡ peerStates pre pid
                   → StepPeerState pid (msgPool pre) (initialised pre) ppre initd' (ppost , msgs)
                   → initialised pre pid ≡ initd
                   → (eInRange : (₋rmamEC ppost) ^∙ rmEpoch < ₋rmamMetaNumEpochs ppost)
                   → Σ (₋rmamMetaNumEpochs ppost ≡ ₋rmamMetaNumEpochs ppre) λ num𝓔s≡ →
                       lookup'' (₋rmamMetaAvailEpochs ppre) (subst ((₋rmamEC ppost) ^∙ rmEpoch <_) num𝓔s≡ eInRange) ≡ lookup'' (₋rmamMetaAvailEpochs ppost) eInRange
  noEpochChangeYet _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  noEpochChangeYet _ ppre≡ (step-msg {(_ , m)} _ _) ini eInRange
     with m
  ...| P p = refl , refl
  ...| V v = refl , refl
  ...| C c = refl , refl

  oldVoteRound≤lvr :  ∀ {pid pk v}{pre : SystemState}
                   → (r : ReachableSystemState pre)
                   → initialised pre pid ≡ initd
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → PeerCanSignForPK (peerStates pre pid) v pid pk
                   → (₋rmamEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋rmamEC (peerStates pre pid)) ^∙ rmLastVotedRound
  oldVoteRound≤lvr {pid = pid'} {pre = pre} (step-s {pre = prev} r (step-peer {pid = pid} cheat@(step-cheat c)))
                    pidIn pkH sig msv vspk eid≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = oldVoteRound≤lvr r (trans (sym (overrideSameVal-correct pid pid')) pidIn) pkH sig msb4 vspk eid≡
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s {pre = prev} r (step-peer {pid = pid} stHon@(step-honest stPeer)))
                   pidIn pkH sig msv vspk eid≡
     with newMsg⊎msgSentB4 r stHon pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with pid ≟ pid'
  ...| no imp = oldVoteRound≤lvr r pidIn pkH sig msb4 vspk eid≡
  ...| yes refl = let ep≡st = noEpochChangeYet r refl stPeer {! pidIn!}
                      lvr≤  = lastVoteRound-mono r refl stPeer {!!} {!ep≡st!}
                      ep≡v  = trans {! ep≡st !} eid≡
                  in ≤-trans (oldVoteRound≤lvr r {!!} pkH sig msb4 {! vspk !} ep≡v) lvr≤

  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s r (step-peer {pid = pid} stHon@(step-honest stPeer)))
                   pidIn pkH sig msv vspk eid≡
     | inj₁ (m∈outs , vspkN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with availEpochsConsistent r {!!} {!!} -- vspk vspkN
  ...| xxx = {!!}


  --         -- Both peers are allowed to sign for the same PK in the same epoch,
  --         -- so they are the same peer
  -- ...| refl
  --    with NodeId-PK-OK-injective (PeerCanSignForPK.𝓔 vspk) ? ? -- (vp-sender-ok vspk) (vp-sender-ok vspkN)
  -- ...| refl rewrite roundManagerPostSt r stPeer refl
  --      = let nvr = newVoteSameEpochGreaterRound r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV
  --        in ≡⇒≤ ((proj₂ ∘ proj₂) nvr)

  -- votesOnce₁ : VO.ImplObligation₁
  -- votesOnce₁ {pid' = pid'} r (step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
  --            pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' eid≡ r≡
  --    with v⊂m
  -- ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
  --                    vspkv' = {!vspkv!} -- ValidSenderForPK⇒ep≡ sv sv' eid≡ vspkv
  --                    rv'<rv = oldVoteRound≤lvr r psI pkH sv' m'mwsb vspkv' eid≡
  --                in ⊥-elim (<⇒≢ (s≤s rv'<rv) (sym r≡))
  -- ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) rewrite cong ₋vSignature v≈rbld
  --      = ⊥-elim (¬msb (qcVotesSentB4 r psI refl qc∈m refl vs∈qc))

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
