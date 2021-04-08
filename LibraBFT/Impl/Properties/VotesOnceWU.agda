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
open import LibraBFT.Impl.Properties.VotesOnce

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnceWU where

  oldVoteRound≤lvr :  ∀ {e pid pk v}{pre : SystemState e}
                   → (r : ReachableSystemState pre)
                   → initialised pre pid ≡ initd
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                   → ValidSenderForPK (availEpochs pre) v pid pk
                   → (₋epEC (peerStates pre pid)) ^∙ epEpoch ≡ (v ^∙ vEpoch)
                   → v ^∙ vRound ≤ (₋epEC (peerStates pre pid)) ^∙ epLastVotedRound
  oldVoteRound≤lvr (step-s r (step-epoch _)) pidIn pkH sig msv vspk ep≡ = {!!}
  oldVoteRound≤lvr {pid = pid'} (step-s r (step-peer {pid = pid} cheat@(step-cheat f c)))
                    pidIn pkH sig msv vspk ep≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     rewrite cheatStepDNMPeerStates₁ {pid = pid} {pid' = pid'} cheat unit
       = oldVoteRound≤lvr r pidIn pkH sig msb4 vspk ep≡
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s r (step-peer {pid = pid} stHon@(step-honest stPeer)))
                   pidIn pkH sig msv vspk ep≡
     with newMsg⊎msgSentB4 r stHon pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
  ...| inj₂ msb4 rewrite msgSameSig msv
     with pid ≟ pid'
  ...| no imp = oldVoteRound≤lvr r pidIn pkH sig msb4 vspk ep≡
  ...| yes refl = let ep≡st = noEpochChangeYet r refl stPeer
                      lvr≤  = lastVoteRound-mono r refl stPeer ep≡st
                      ep≡v  = trans ep≡st ep≡
                  in ≤-trans (oldVoteRound≤lvr r pidIn pkH sig msb4 vspk ep≡v) lvr≤
  oldVoteRound≤lvr {pid = pid'} {pre = pre}
                   step@(step-s r (step-peer {pid = pid} stHon@(step-honest stPeer)))
                   pidIn pkH sig msv vspk ep≡
     | inj₁ (m∈outs , vspkN , newV)
     with sameHonestSig⇒sameVoteData pkH (msgSigned msv) sig (msgSameSig msv)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre step hb)
  ...| inj₂ refl
     with sameEpoch⇒sameEC vspk vspkN refl
          -- Both peers are allowed to sign for the same PK, so they are the same peer
  ...| refl
     with NodeId-PK-OK-injective (vp-ec vspk) (vp-sender-ok vspk) (vp-sender-ok vspkN)
  ...| refl rewrite eventProcessorPostSt r stPeer refl
       = let nvr = newVoteSameEpochGreaterRound r stPeer (msg⊆ msv) m∈outs (msgSigned msv) newV
         in ≡⇒≤ ((proj₂ ∘ proj₂) nvr)


  votesOnce₁ : VO.ImplObligation₁
  votesOnce₁ {pid' = pid'} r (step-msg {_ , P m} _ psI) {v' = v'} {m' = m'}
             pkH v⊂m (here refl) sv ¬msb vspkv v'⊂m' m'∈pool sv' ep≡ r≡
     with v⊂m
  ...| vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                     vspkv' = ValidSenderForPK⇒ep≡ sv sv' ep≡ vspkv
                     rv'<rv = oldVoteRound≤lvr r psI pkH sv' m'mwsb vspkv' ep≡
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
