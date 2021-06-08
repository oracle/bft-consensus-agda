{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Concrete.System
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

-- This module contains placeholders for the future analog of the
-- corresponding VotesOnce property.  Defining the implementation
-- obligation and proving that it is an invariant of an implementation
-- is a substantial undertaking.  We are working first on proving the
-- simpler VotesOnce property to settle down the structural aspects
-- before tackling the harder semantic issues.
module LibraBFT.Concrete.Properties.PreferredRound (𝓔 : EpochConfig) where
 import      LibraBFT.Abstract.Records UID _≟UID_ NodeId  𝓔 (ConcreteVoteEvidence 𝓔) as Abs
 open import LibraBFT.Concrete.Obligations.PreferredRound 𝓔 (ConcreteVoteEvidence 𝓔)
 open WithAbsVote 𝓔
 open PeerCanSignForPK
 open PeerCanSignForPKinEpoch

 -- As with VotesOnce, we will have two implementation obligations, one for when v is sent by the
 -- step and v' has been sent before, and one for when both are sent by the step.

 ImplObligation₁ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₁ =
   ∀{pid pid' s' outs pk}{pre : SystemState}
   → (r : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → ∀{mbr v vabs m v' v'abs m'}
   → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v'  ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- And if there exists another v' that has been sent before
   → v ⊂Msg m → (pid' , m) ∈ (msgPool pre)
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v and v' share the same epoch
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   -- and v is for a smaller round
   → v ^∙ vRound < v' ^∙ vRound
   -- and vabs* are the abstract Votes for v and v'
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → (c2 : Cand-3-chain-vote vabs)
   -- then the round of the block that v' votes for is at least the round of
   -- the grandparent of the block that v votes for (i.e., the preferred round rule)
   → Σ (VoteParentData v'abs)
           (λ vp → Cand-3-chain-head-round c2 ≤ Abs.round (vpParent vp))

 -- Similarly in case the same step sends both v and v'
 ImplObligation₂ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₂ =
   ∀{pid s' outs pk}{pre : SystemState}
   → (r  : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → ∀{mbr v vabs m v' v'abs m'}
   → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v pid pk
   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound < v' ^∙ vRound
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → (c2 : Cand-3-chain-vote vabs)
   → Σ (VoteParentData v'abs)
           (λ vp → Cand-3-chain-head-round c2 ≤ Abs.round (vpParent vp))

  -- Next, we prove that given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-PR1 : ImplObligation₁)
   (Impl-PR2 : ImplObligation₂)
   where
  -- Any reachable state satisfies the PR rule for any epoch in the system.
  module _ (st : SystemState)(r : ReachableSystemState st) where
   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr
   -- Bring in intSystemState
   open        PerState st r
   open        PerEpoch 𝓔
   open import LibraBFT.Concrete.Obligations.PreferredRound 𝓔 (ConcreteVoteEvidence 𝓔) as PR

   v-cand-3-chain⇒0<roundv : ∀ {v mbr vabs} {st : SystemState}
                           → (r : ReachableSystemState st)
                           → α-ValidVote 𝓔 v mbr ≡ vabs
                           → PR.Cand-3-chain-vote vabs
                           → 0 < v ^∙ vRound

   PreferredRoundProof :
      ∀ {v v' vabs v'abs pk mbr} {st : SystemState}
      → (r : ReachableSystemState st)
      → Meta-Honest-PK pk
      → (vv  : WithVerSig pk v)  → MsgWithSig∈ pk (ver-signature vv)  (msgPool st)
      → (vv' : WithVerSig pk v') → MsgWithSig∈ pk (ver-signature vv') (msgPool st)
      → v ^∙ vEpoch ≡ v' ^∙ vEpoch
      → v ^∙ vRound < v' ^∙ vRound
      → α-ValidVote 𝓔 v  mbr ≡ vabs
      → α-ValidVote 𝓔 v' mbr ≡ v'abs
      → (c3 : PR.Cand-3-chain-vote vabs)
      → Σ (PR.VoteParentData v'abs)
           (λ vp → PR.Cand-3-chain-head-round c3 ≤ Abs.round (vpParent vp))
   PreferredRoundProof step-0 _ _ msv = ⊥-elim (¬Any[] (msg∈pool msv))
   PreferredRoundProof {v} step@(step-s r theStep) pkH vv msv vv' msv' eid≡ rv<rv' absv absv' c3
      with msgSameSig msv | msgSameSig msv'
   ...| refl | refl
      with sameSig⇒sameVoteDataNoCol (msgSigned msv)  vv  (msgSameSig msv )
         | sameSig⇒sameVoteDataNoCol (msgSigned msv') vv' (msgSameSig msv')
   ...| refl | refl
      with ∈GenInfo? (₋vSignature (msgPart msv)) | ∈GenInfo? (₋vSignature (msgPart msv'))
   ...| yes init  | yes init' =  let rv≡0  = genVotesRound≡0 vv  init
                                     rv'≡0 = genVotesRound≡0 vv' init'
                                 in ⊥-elim (<⇒≢ rv<rv' (trans rv≡0 (sym rv'≡0)))
   ...| yes init  | no  ¬init = let 0≡rv = sym (genVotesRound≡0 vv  init)
                                    0<rv = v-cand-3-chain⇒0<roundv {v} (step-s r theStep) absv c3
                                in ⊥-elim (<⇒≢ 0<rv 0≡rv)
   ...| no  ¬init | yes init  = let 0≡rv' = sym (genVotesRound≡0 vv' init)
                                in ⊥-elim (<⇒≱ rv<rv' (subst (v ^∙ vRound ≥_) 0≡rv' z≤n))
   ...| no  ¬init | no ¬init'
      with theStep
   ...| step-peer cheat@(step-cheat c)
      with ¬cheatForgeNew cheat refl unit pkH msv  ¬init
         | ¬cheatForgeNew cheat refl unit pkH msv' ¬init'
   ...| msb4 | m'sb4
      with  msgSameSig msb4 | msgSameSig m'sb4
   ...| refl | refl
        = PreferredRoundProof r pkH vv msb4 vv' m'sb4 eid≡ rv<rv' absv absv' c3
   PreferredRoundProof {v} step@(step-s r theStep) pkH vv msv vv' msv' eid≡ rv<rv' absv absv' c3
      | refl | refl
      | refl | refl
      | no  ¬init | no ¬init'
      | step-peer (step-honest stPeer)
      with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv)  ¬init  (msg⊆ msv)  (msg∈pool msv)
         | newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv') ¬init' (msg⊆ msv') (msg∈pool msv')
   ...| inj₂ msb4                   | inj₂ m'sb4
        = PreferredRoundProof r pkH vv msb4 vv' m'sb4 eid≡ rv<rv' absv absv' c3
   ...| inj₁ (m∈outs , vspk , newV) | inj₁ (m'∈outs , v'spk , newV')
        = Impl-PR2 r stPeer pkH (msg⊆ msv) m∈outs (msgSigned msv) ¬init newV vspk
                   (msg⊆ msv') m'∈outs (msgSigned msv') ¬init' newV' v'spk eid≡ rv<rv' absv absv' c3
   ...| inj₁ (m∈outs , vspk , newV) | inj₂ m'sb4
      with sameSig⇒sameVoteData (msgSigned m'sb4) vv' (msgSameSig m'sb4)
   ...| inj₁ hb   = ⊥-elim (meta-sha256-cr hb)
   ...| inj₂ refl
        = {! We should get to a contradiction here because of the increasing round rule. Notice that if
             v is being send now and v' was sent before (by the same peer), then by the increasing round
             rule we should have that v'.Round < v.Round, but we have that v.Round < v'.Round. Therefore
             we cannot call the Impl-PR1 switching the arguments (as we did on VotesOnceProof). !}
   PreferredRoundProof {v} step@(step-s r theStep) pkH vv msv vv' msv' eid≡ rv<rv' absv absv' c3
      | refl | refl
      | refl | refl
      | no  ¬init | no ¬init'
      | step-peer (step-honest stPeer)
      | inj₂ msb4                   | inj₁ (m'∈outs , v'spk , newV')
      with sameSig⇒sameVoteData (msgSigned msb4) vv (msgSameSig msb4)
   ...| inj₁ hb   = ⊥-elim (meta-sha256-cr hb)
   ...| inj₂ refl
        =  Impl-PR1 r stPeer pkH (msg⊆ msv') m'∈outs (msgSigned msv') ¬init' newV' v'spk
                    (msg⊆ msb4) (msg∈pool msb4) (msgSigned msb4) (¬subst ¬init (msgSameSig msb4))
                    eid≡ rv<rv' absv absv' c3


   prr : PR.Type intSystemState
   prr honα refl sv refl sv' c2 round<
     with vmsg≈v (vmFor sv) | vmsg≈v (vmFor sv')
   ...| refl | refl
       = let ver = vmsgSigned (vmFor sv)
             mswsv = mkMsgWithSig∈ (nm (vmFor sv)) (cv (vmFor sv)) (cv∈nm (vmFor sv))
                                    _ (nmSentByAuth sv) (vmsgSigned (vmFor sv)) refl
             ver' = vmsgSigned (vmFor sv')
             mswsv' = mkMsgWithSig∈ (nm (vmFor sv')) (cv (vmFor sv')) (cv∈nm (vmFor sv'))
                                     _ (nmSentByAuth sv') (vmsgSigned (vmFor sv')) refl
             epoch≡ = trans (vmsgEpoch (vmFor sv)) (sym (vmsgEpoch (vmFor sv')))
         in PreferredRoundProof r honα ver mswsv ver' mswsv' epoch≡ round< refl refl c2
