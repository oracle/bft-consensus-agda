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
open import LibraBFT.Concrete.Properties.Common
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
 open import LibraBFT.Concrete.Properties.VotesOnce 𝓔 as VO
 open WithAbsVote 𝓔
 open PeerCanSignForPK
 open PeerCanSignForPKinEpoch

 -- As with VotesOnce, we will have two implementation obligations, one for when v is sent by the
 -- step and v' has been sent before, and one for when both are sent by the step.

 PR-ImplObligation₁ : Set (ℓ+1 ℓ-RoundManager)
 PR-ImplObligation₁ =
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
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- And if there exists another v' that has been sent before
   → v ⊂Msg m → (pid' , m) ∈ (msgPool pre)
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v and v' share the same epoch
   → v ^∙  vEpoch ≡ v' ^∙ vEpoch
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
     ⊎ (VoteForRound∈ pk (v' ^∙ vRound) (v' ^∙ vEpoch) (v' ^∙ vProposedId) (msgPool pre))


 -- Similarly in case the same step sends both v and v'
 PR-ImplObligation₂ : Set (ℓ+1 ℓ-RoundManager)
 PR-ImplObligation₂ =
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
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) -- ∄[ v'' ] VoteForRound∈ ... ?
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v pid pk
   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre)) -- ∄[ v'' ] VoteForRound∈ ... ?
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
 module PR-Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-IRO : VO.IncreasingRoundObligation)
   (Impl-PR1 : PR-ImplObligation₁)
   (Impl-PR2 : PR-ImplObligation₂)
   where
  -- Any reachable state satisfies the PR rule for any epoch in the system.
  module _ (st : SystemState)(r : ReachableSystemState st) where
   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr
   -- Bring in intSystemState
   open        PerState st r
   open        PerEpoch 𝓔
   open        ConcreteCommonProperties st r


   α-ValidVote-trans : ∀ {pk mbr vabs pool} (v : Vote)
                     → α-ValidVote 𝓔 v mbr ≡ vabs
                     → (vfr : VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch)
                                            (v ^∙ vProposedId) pool)
                     → α-ValidVote 𝓔 (msgVote vfr) mbr ≡ vabs
   α-ValidVote-trans v₁ refl vfr
     with msgRound≡ vfr | msgEpoch≡ vfr | msgBId≡ vfr
   ...| refl | refl | refl = refl

   PreferredRoundProof :
      ∀ {pk round₁ round₂ epoch bId₁ bId₂ v₁abs v₂abs mbr} {st : SystemState}
      → ReachableSystemState st
      → Meta-Honest-PK pk
      → (v₁ : VoteForRound∈ pk round₁ epoch bId₁ (msgPool st))
      → (v₂ : VoteForRound∈ pk round₂ epoch bId₂ (msgPool st))
      → round₁ < round₂
      → α-ValidVote 𝓔 (msgVote v₁) mbr ≡ v₁abs
      → α-ValidVote 𝓔 (msgVote v₂) mbr ≡ v₂abs
      → (c3 : Cand-3-chain-vote v₁abs)
      → Σ (VoteParentData v₂abs)
            (λ vp → Cand-3-chain-head-round c3 ≤ Abs.round (vpParent vp))
   PreferredRoundProof step@(step-s r theStep) pkH v₁ v₂ r₁<r₂ refl refl c3
      with msgRound≡ v₁ | msgEpoch≡ v₁ | msgBId≡ v₁
         | msgRound≡ v₂ | msgEpoch≡ v₂ | msgBId≡ v₂
   ...| refl | refl | refl | refl | refl | refl
      with ∈GenInfo? (₋vSignature (msgVote v₁)) | ∈GenInfo? (₋vSignature (msgVote v₂))
   ...| yes init₁  | yes init₂  = let r₁≡0 = genVotesRound≡0 (msgSigned v₁) init₁
                                      r₂≡0 = genVotesRound≡0 (msgSigned v₂) init₂
                                  in ⊥-elim (<⇒≢ r₁<r₂ (trans r₁≡0 (sym r₂≡0)))
   ...| yes init₁  | no  ¬init₂ = let 0≡rv = sym (genVotesRound≡0 (msgSigned v₁) init₁)
                                      0<rv = v-cand-3-chain⇒0<roundv c3
                                  in ⊥-elim (<⇒≢ 0<rv 0≡rv)
   ...| no  ¬init₁ | yes init₂  = let 0≡r₂ = sym (genVotesRound≡0 (msgSigned v₂) init₂)
                                      r₁   = msgVote v₁ ^∙ vRound
                                  in ⊥-elim (<⇒≱ r₁<r₂ (subst (r₁ ≥_) 0≡r₂ z≤n))
   ...| no  ¬init₁ | no ¬init₂
      with theStep
   ...| step-peer cheat@(step-cheat c)
        = let m₁sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned v₁) (msg⊆ v₁) (msg∈pool v₁) ¬init₁
              m₂sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned v₂) (msg⊆ v₂) (msg∈pool v₂) ¬init₂
              v₁sb4 = msgSentB4⇒VoteRound∈ (msgSigned v₁) m₁sb4
              v₂sb4 = msgSentB4⇒VoteRound∈ (msgSigned v₂) m₂sb4
              v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
              v₂abs = α-ValidVote-trans (msgVote v₂) refl v₂sb4
          in PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs v₂abs c3
   ...| step-peer (step-honest stP)
      with ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned v₁))
                  (newMsg⊎msgSentB4 r stP pkH (msgSigned v₁) ¬init₁  (msg⊆ v₁) (msg∈pool v₁))
         | ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned v₂))
                  (newMsg⊎msgSentB4 r stP pkH (msgSigned v₂) ¬init₂ (msg⊆ v₂) (msg∈pool v₂))
   ...| inj₂ v₁sb4                | inj₂ v₂sb4
        = let v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
              v₂abs = α-ValidVote-trans (msgVote v₂) refl v₂sb4
          in PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs v₂abs c3
   ...| inj₁ (m₁∈outs , v₁pk , newV₁) | inj₁ (m₂∈outs , v₂pk , newV₂)
        = Impl-PR2 r stP pkH (msg⊆ v₁) m₁∈outs (msgSigned v₁) ¬init₁ newV₁ v₁pk (msg⊆ v₂)
                   m₂∈outs (msgSigned v₂) ¬init₂ newV₂ v₂pk refl r₁<r₂ refl refl c3
   ...| inj₁ (m₁∈outs , v₁pk , _) | inj₂ v₂sb4
        = let round≡ = trans (msgRound≡ v₂sb4) (msgRound≡ v₂)
              ¬genV₂ = ¬Gen∧Round≡⇒¬Gen step pkH v₂ ¬init₂ (msgSigned v₂sb4) round≡
              epoch≡ = sym (msgEpoch≡ v₂sb4)
          in either (λ r₂<r₁ → ⊥-elim (<⇒≯ r₁<r₂ (<-transʳ (≡⇒≤ (sym round≡)) r₂<r₁)))
                    (λ v₁sb4 → let v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
                                   v₂abs = α-ValidVote-trans (msgVote v₂) refl v₂sb4
                               in PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs v₂abs c3)
                    (Impl-IRO r stP pkH (msg⊆ v₁) m₁∈outs (msgSigned v₁) ¬init₁ v₁pk
                              (msg⊆ v₂sb4) (msg∈pool v₂sb4) (msgSigned v₂sb4) ¬genV₂ epoch≡)
   ...| inj₂ v₁sb4                | inj₁ (m₂∈outs , v₂pk , _)
        = let rv₁<r₂ = <-transʳ (≡⇒≤ (msgRound≡ v₁sb4)) r₁<r₂
              round≡ = trans (msgRound≡ v₁sb4) (msgRound≡ v₁)
              ¬genV₁ = ¬Gen∧Round≡⇒¬Gen step pkH v₁ ¬init₁ (msgSigned v₁sb4) round≡
              v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
          in either id
                    (λ v₂sb4 → let v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
                                   v₂abs = α-ValidVote-trans (msgVote v₂) refl v₂sb4
                               in PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs v₂abs c3)
                    (Impl-PR1 r stP pkH (msg⊆ v₂) m₂∈outs (msgSigned v₂) ¬init₂ v₂pk
                              (msg⊆ v₁sb4) (msg∈pool v₁sb4) (msgSigned v₁sb4) ¬genV₁
                              (msgEpoch≡ v₁sb4) rv₁<r₂ v₁abs refl c3)


   prr : Type intSystemState
   prr honα refl sv refl sv' c2 round<
     with vmsg≈v (vmFor sv) | vmsg≈v (vmFor sv')
   ...| refl | refl
       = let v₁ = mkVoteForRound∈ (nm (vmFor sv)) (cv ((vmFor sv))) (cv∈nm (vmFor sv))
                                  (vmSender sv) (nmSentByAuth sv) (vmsgSigned (vmFor sv))
                                  (vmsgEpoch (vmFor sv)) refl refl
             v₂ = mkVoteForRound∈ (nm (vmFor sv')) (cv (vmFor sv')) (cv∈nm (vmFor sv'))
                                  (vmSender sv') (nmSentByAuth sv') (vmsgSigned (vmFor sv'))
                                  (vmsgEpoch (vmFor sv')) refl refl
         in PreferredRoundProof r honα v₁ v₂ round< refl refl c2
