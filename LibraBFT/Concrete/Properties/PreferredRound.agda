{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.Records as LCR
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
open import Optics.All

open        EpochConfig

-- This module contains placeholders for the future analog of the
-- corresponding VotesOnce property.  Defining the implementation
-- obligation and proving that it is an invariant of an implementation
-- is a substantial undertaking.  We are working first on proving the
-- simpler VotesOnce property to settle down the structural aspects
-- before tackling the harder semantic issues.
module LibraBFT.Concrete.Properties.PreferredRound (iiah : SystemInitAndHandlers ℓ-RoundManager ConcSysParms) (𝓔 : EpochConfig) where
 open        LibraBFT.ImplShared.Consensus.Types.EpochDep.WithEC
 import      LibraBFT.Abstract.Records         UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔) as Abs
 import      LibraBFT.Abstract.Records.Extends UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔) as Ext
 open import LibraBFT.Abstract.RecordChain     UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔)
 open import LibraBFT.Abstract.System          UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔)
 open import LibraBFT.Concrete.Intermediate                      𝓔 (ConcreteVoteEvidence 𝓔)
 open import LibraBFT.Concrete.Obligations.PreferredRound        𝓔 (ConcreteVoteEvidence 𝓔)
 open        SystemTypeParameters ConcSysParms
 open        SystemInitAndHandlers iiah
 open        ParamsWithInitAndHandlers iiah
 open import LibraBFT.ImplShared.Util.HashCollisions iiah
 open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms iiah PeerCanSignForPK PeerCanSignForPK-stable
 open import LibraBFT.Concrete.Properties.Common iiah 𝓔

 open PerEpoch    𝓔
 open WithAbsVote 𝓔
 open LCR.WithEC  𝓔
 open PerState
 open PerReachableState

{- ImplObl-RC : Set (ℓ+1 ℓ-RoundManager)
 ImplObl-RC =
   ∀{pid s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → let s = peerStates pre pid in
     (sps : StepPeerState pid (msgPool pre) (initialised pre) s (s' , outs))
   → ∀{v m} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v ⊂Msg m → send m ∈ outs
   → (wvs : WithVerSig pk v)
   → (¬ ∈BootstrapInfo bootstrapInfo (ver-signature wvs))
   → v ^∙ vEpoch ≡ epoch 𝓔
   → ∃[ mbr ] ( getPubKey 𝓔 mbr ≡ pk
              × Σ (VoteExtends (α-ValidVote 𝓔 v mbr))
                  λ vExt → let b = VoteExtends.veBlock vExt in
                            Σ (RecordChain (Abs.B b)) {! All-InSys !} )
-}

 -- As with VotesOnce, we will have two implementation obligations, one for when v is sent by the
 -- step and v' has been sent before, and one for when both are sent by the step.

 ImplObligation₁ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₁ =
   ∀{pid pid' s' outs pk}{pre : SystemState}
   → (r : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → let post = StepPeer-post {pre = pre} (step-honest sps) in
     ∀{mbr v vabs m v' v'abs m'}
   → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v'  ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈BootstrapInfo bootstrapInfo (ver-signature sig'))
   -- If v is really new and valid
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- And if there exists another v' that has been sent before
   → v ⊂Msg m → (pid' , m) ∈ (msgPool pre)
   → (sig : WithVerSig pk v) → ¬ (∈BootstrapInfo bootstrapInfo (ver-signature sig))
   -- If v and v' share the same epoch
   → v ^∙  vEpoch ≡ v' ^∙ vEpoch
   -- and v is for a smaller round
   → v ^∙ vRound < v' ^∙ vRound
   -- and vabs* are the abstract Votes for v and v'
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → (c2 : Cand-3-chain-vote (intSystemState post) vabs)
   -- then the round of the block that v' votes for is at least the round of
   -- the grandparent of the block that v votes for (i.e., the preferred round rule)
   → Σ (VoteParentData (intSystemState post) v'abs)
           (λ vp → Cand-3-chain-head-round (intSystemState post) c2 ≤ Abs.round (vpParent vp))
     ⊎ (VoteForRound∈ pk (v' ^∙ vRound) (v' ^∙ vEpoch) (v' ^∙ vProposedId) (msgPool pre))

 -- Similarly in case the same step sends both v and v'
 ImplObligation₂ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₂ =
   ∀{pid s' outs pk}{pre : SystemState}
   → (r  : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → let post = StepPeer-post {pre = pre} (step-honest sps) in
     ∀{mbr v vabs m v' v'abs m'}
   → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈BootstrapInfo bootstrapInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) -- ∄[ v'' ] VoteForRound∈ ... ?
   → PeerCanSignForPK post v pid pk
   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈BootstrapInfo bootstrapInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre)) -- ∄[ v'' ] VoteForRound∈ ... ?
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound < v' ^∙ vRound
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → (c2 : Cand-3-chain-vote (intSystemState post) vabs)
   → Σ (VoteParentData (intSystemState post) v'abs)
           (λ vp → Cand-3-chain-head-round (intSystemState post) c2 ≤ Abs.round (vpParent vp))

 module _ where
   open InSys iiah

   stepPreservesVoteParentData : ∀ {st0 st1 v}
     → Step st0 st1
     → (vpd : VoteParentData (intSystemState st0) v)
     → Σ (VoteParentData (intSystemState st1) v)
         λ vpd' → vpParent vpd' ≡ vpParent vpd
   stepPreservesVoteParentData {st0} {st1} theStep vpd
      with vpd
   ...| (record { vpExt        = vpExt
                ; vpBlock∈sys  = vpBlock∈sys
                ; vpParent     = vpParent
                ; vpParent∈sys = vpParent∈sys
                ; vpExt'       = vpExt'
                ; vpMaybeBlock = vpMaybeBlock
                }) = (record
                     { vpExt        = vpExt
                     ; vpBlock∈sys  = stable theStep vpBlock∈sys
                     ; vpParent     = vpParent
                     ; vpParent∈sys = stable theStep vpParent∈sys
                     ; vpExt'       = vpExt'
                     ; vpMaybeBlock = transp-vpmb vpMaybeBlock
                     }) , refl
     where transp-vpmb : ∀ {r}
                         → VoteParentData-BlockExt (intSystemState st0) r
                         → VoteParentData-BlockExt (intSystemState st1) r
           transp-vpmb vpParent≡I = vpParent≡I
           transp-vpmb (vpParent≡Q x x₁) = vpParent≡Q x (stable theStep x₁)

 module Proof
   (sps-corr : StepPeerState-AllValidParts)   -- Bring in newMsg⊎msgSentB4
   (Impl-bsvr : ImplObl-bootstrapVotesRound≡0)
   (Impl-nvr≢0 : ImplObl-NewVoteRound≢0)
   (Impl-∈BI? : (sig : Signature) → Dec (∈BootstrapInfo bootstrapInfo sig))
   (Impl-IRO : IncreasingRoundObligation)
   (Impl-PR1 : ImplObligation₁)
   (Impl-PR2 : ImplObligation₂)
    where
  module _ {st : SystemState}(r : ReachableSystemState st) (𝓔-∈sys : EpochConfig∈Sys st 𝓔) where
   open        Structural sps-corr
   open        ConcreteCommonProperties st r sps-corr Impl-bsvr Impl-nvr≢0
   open        IntermediateSystemState
   open        All-InSys-props

   α-ValidVote-trans : ∀ {pk mbr vabs pool} (v : Vote)
                     → α-ValidVote 𝓔 v mbr ≡ vabs
                     → (vfr : VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch)
                                            (v ^∙ vProposedId) pool)
                     → α-ValidVote 𝓔 (msgVote vfr) mbr ≡ vabs
   α-ValidVote-trans v₁ refl vfr
     with msgRound≡ vfr | msgEpoch≡ vfr | msgBId≡ vfr
   ...| refl | refl | refl = refl

   -- To prove this, we observe that cheaters can't introduce a VoteForRound∈ for an honest PK.  We
   -- will also require an additional implementation obligation.  It may simply be that Votes sent
   -- satisy IsValidVote, but the question is where do we maintain evidence that such a RecordChain
   -- exists for any Block we may vote for?
   -- postulate
   voteForRound-RC : ∀ {pk vabs}{st : SystemState}
                     → Meta-Honest-PK pk
                     → ReachableSystemState st
                     → (v4r : VoteForRound∈ pk (abs-vRound vabs) (epoch 𝓔) (abs-vBlockUID vabs) (msgPool st))
                     → 0 < abs-vRound vabs
                     → ∃[ b ] ( Abs.bId b ≡ abs-vBlockUID vabs
                              × Σ (RecordChain (Abs.B b)) (All-InSys (InSys (intSystemState st))))
   voteForRound-RC {pk} {abs} {st} hpk (step-s preReach (step-peer (step-honest sps))) v4r 0<r
      rewrite sym $ msgRound≡ v4r
      with newMsg⊎msgSentB4 {sndr = msgSender v4r} preReach sps hpk (msgSigned v4r)
                            -- TODO-1: refactor for DRY, see below
                            (λ ∈bsi → ⊥-elim (<⇒≢ 0<r $ sym $ Impl-bsvr (msgSigned v4r) ∈bsi)) (msg⊆ v4r)
                            (msg∈pool v4r)
   ... | inj₁ x = obm-dangerous-magic' "TODO"
   ... | inj₂ y = obm-dangerous-magic' "TODO"
   voteForRound-RC {pk} {vabs} hpk (step-s {pre = pre} preReach sps@(step-peer (step-cheat {pid} x))) v4r 0<r
      with VoteRound∈⇒msgSent v4r
   ...| msgb4 , refl , refl
      with ¬cheatForgeNew {st = pre} (step-cheat x) refl unit hpk msgb4
                          λ ∈bsi → ⊥-elim (<⇒≢ 0<r $ sym $ Impl-bsvr (msgSigned msgb4) ∈bsi)
   ...| mwsb4
      with sameSig⇒sameVoteData (msgSigned mwsb4) (msgSigned v4r) (msgSameSig mwsb4)
   ...| inj₁ hb = ⊥-elim $ meta-no-collision preReach hb -- TODO-2: refine sameSig⇒samevotedata to
                                                         -- enable tying collision to specific state
                                                         -- so we can use meta-no-collision-in-sys
   ...| inj₂ svd
      with msgSentB4⇒VoteRound∈ (msgSigned v4r) mwsb4'
         where
           mwsb4' : _
           mwsb4' rewrite
                    trans (cong (_^∙ vdProposed ∙ biEpoch) $ sym svd) (msgEpoch≡ v4r) |
                    msgBId≡ v4r |
                    msgSameSig mwsb4 = mwsb4
   ...| v4r' , refl
      with voteForRound-RC {pk} {vabs} hpk preReach v4r'' 0<r
         where
           v4r'' : VoteForRound∈ pk (abs-vRound vabs) (epoch 𝓔) (abs-vBlockUID vabs) (msgPool pre)
           v4r'' rewrite sym (msgEpoch≡ v4r) | sym (msgRound≡ v4r) | sym (msgBId≡ v4r) = v4r'
   ...| b , refl , rc , ais = b , refl , rc , InSys.ais-stable iiah sps rc ais

   open _α-Sent_
   open _BlockDataInjectivityProps_

   Abs2ImplCollision : ∀ {ab1 ab2 : Abs.Block}{post}
                     → (rPost : ReachableSystemState post)
                     → InSys (intSystemState post) (Abs.B ab1)
                     → InSys (intSystemState post) (Abs.B ab2)
                     → ab1 ≢ ab2
                     → Abs.bId ab1 ≡ Abs.bId ab2
                     → HashCollisionFound rPost
   Abs2ImplCollision rPost (ws ep≡1 m1∈pool (b∈NM {cb1} {pm1} refl refl bidcorr1))
                           (ws ep≡2 m2∈pool (b∈NM {cb2} {pm2} refl refl bidcorr2)) neq absIds≡ =
     msgmsgHC {r = rPost} (inP m1∈pool (inPM (inB {b = cb1}))) (inP m2∈pool (inPM (inB {b = cb2}))) hashes≡ bsls≢
     where
       -- TODO-2: Some of the properties should be factored out for reuse, maybe into Common?
       bIds≡ : _
       bIds≡ = trans (trans (α-Block-bid≡ cb1) absIds≡) (sym (α-Block-bid≡ cb2))

       hashes≡ : _
       hashes≡ = trans (trans bidcorr1 bIds≡) (sym bidcorr2)

       rnds≡ : ∀ {cb1 cb2} → (cb1 ^∙ bBlockData) BlockDataInjectivityProps (cb2 ^∙ bBlockData)
               → Abs.bRound (α-Block cb1) ≡ Abs.bRound (α-Block cb2)
       rnds≡ {cb1} {cb2} injprops = trans (sym (α-Block-rnd≡ cb1)) (trans (bdInjRound injprops) (α-Block-rnd≡ cb2))

       propBlock : ∀ {cb pm} → pm ^∙ pmProposal ≡ cb
                   → cb ^∙ bId ≡ pm ^∙ pmProposal ∙ bId
       propBlock refl = refl

       prevQCs≡ : ∀ {cb1 cb2}
                  → (cb1 ^∙ bBlockData) BlockDataInjectivityProps (cb2 ^∙ bBlockData)
                  → Abs.bPrevQC (α-Block cb1) ≡ Abs.bPrevQC (α-Block cb2)
       prevQCs≡ {cb1} {cb2} injprops
          with cb1 ^∙ bBlockData ∙ bdBlockType | inspect
               (cb1 ^∙_) (bBlockData ∙ bdBlockType)
       ...| Genesis      | [ R ] rewrite R                    = sym (α-Block-prevqc≡-Gen  {cb2} (bdInjBTGen injprops R))
       ...| Proposal _ _ | [ R ] rewrite R | bdInjVD injprops = sym (α-Block-prevqc≡-Prop {cb2} (trans (sym $ bdInjBTProp injprops R) R))
       ...| NilBlock     | [ R ] rewrite R | bdInjBTNil injprops R | bdInjVD injprops = refl

       bsls≢ : _
       bsls≢ _
          with hashBD-inj hashes≡
       ...| injprops = neq (Abs.Block-η
                              (rnds≡ {cb1} {cb2} injprops)
                              absIds≡
                              (prevQCs≡ {cb1} {cb2} injprops))

   Cand-3-chain-vote-b4 : ∀ {pk vabs}{pre : SystemState}{pid st' outs sp}
                          → Meta-Honest-PK pk
                          → ReachableSystemState pre
                          → let post = StepPeer-post {pid}{st'}{outs}{pre} sp in
                            (c2 : Cand-3-chain-vote (intSystemState post) vabs)
                            → (v4r : VoteForRound∈ pk (abs-vRound vabs) (epoch 𝓔) (abs-vBlockUID vabs) (msgPool pre))
                            → Σ (Cand-3-chain-vote (intSystemState pre) vabs)
                                 λ c2' → Cand-3-chain-head-round (intSystemState post) c2
                                       ≡ Cand-3-chain-head-round (intSystemState pre ) c2'
   Cand-3-chain-vote-b4 {pk} {vabs} {pre} {pid} {st'} {outs} {sp} pkH r
                        c3@(mkCand3chainvote (mkVE veBlock refl refl) c3Blk∈sys₁ qc₁ qc←b₁ rc₁ rc∈sys₁ n₁ is-2chain₁) v4r
      with v-cand-3-chain⇒0<roundv  (intSystemState $ StepPeer-post {pid}{st'}{outs}{pre} sp)
   ...| 0<r
      with voteForRound-RC {vabs = vabs} pkH r v4r (0<r c3)
   ...| b , refl , rcb , ais
      with veBlock Abs.≟Block b
   ...| no   neq = ⊥-elim (meta-no-collision-in-sys postR hcf)
        where
          post    = StepPeer-post sp
          theStep = step-peer sp
          postR   = step-s r theStep
          hcf = Abs2ImplCollision postR c3Blk∈sys₁ (InSys.stable iiah theStep (ais here)) neq refl
   ...| yes refl
      with RecordChain-irrelevant rcb (step rc₁ qc←b₁)
   ...| inj₁ (((b1 , b2) , neq , absIds≡) , b1∈rcb , b2∈rc1ext) = ⊥-elim (meta-no-collision-in-sys postR (hcf b2∈rc1ext))
      where
         post    = StepPeer-post sp
         theStep = step-peer sp
         postR   = step-s r theStep

         inSys1  = InSys.stable iiah theStep $ ais b1∈rcb
         inSys2 : _ → _
         inSys2 here = c3Blk∈sys₁
         inSys2 (there .qc←b₁ b2∈rc1ext) = rc∈sys₁ b2∈rc1ext

         hcf : _ → _
         hcf b2∈rc1ext = Abs2ImplCollision postR inSys1 (inSys2 b2∈rc1ext) neq absIds≡
   ...| inj₂ (eq-step {r₀ = .(Abs.B b)} {r₁ = .(Abs.B b)} rc0 rc1 b≈b
                      ext0@(Ext.I←B _ prevNothing)
                      ext1@(Ext.Q←B _ prevJust)
                      rcrest≈) = absurd just _ ≡ nothing case trans prevJust prevNothing of λ ()
   ...| inj₂ (eq-step {r₀ = .(Abs.B b)} {r₁ = .(Abs.B b)} rc0 rc1 b≈b
                      ext0@(Ext.Q←B {qc0} {.b} _ _)
                      ext1@(Ext.Q←B {qc1} {.b} _ _) rcrest≈) = newc3 , rnds≡
          where

            newc3 = mkCand3chainvote (mkVE b refl refl)
                                     (ais here)
                                     qc0
                                     ext0
                                     rc0
                                     (ais ∘ (_∈RC-simple_.there ext0))
                                     n₁
                                     (transp-𝕂-chain (≈RC-sym rcrest≈) is-2chain₁)
            rnds≡ = cong Abs.bRound $ kchainBlock-≈RC is-2chain₁ (suc zero) (≈RC-sym rcrest≈)

   PreferredRoundProof :
      ∀ {pk round₁ round₂ bId₁ bId₂ v₁abs v₂abs mbr} {st : SystemState}
      → ReachableSystemState st
      → Meta-Honest-PK pk
      → (v₁ : VoteForRound∈ pk round₁ (epoch 𝓔) bId₁ (msgPool st))
      → (v₂ : VoteForRound∈ pk round₂ (epoch 𝓔) bId₂ (msgPool st))
      → round₁ < round₂
      → α-ValidVote 𝓔 (msgVote v₁) mbr ≡ v₁abs
      → α-ValidVote 𝓔 (msgVote v₂) mbr ≡ v₂abs
      → (c3 : Cand-3-chain-vote (intSystemState st) v₁abs)
      → Σ (VoteParentData (intSystemState st) v₂abs)
            (λ vp → Cand-3-chain-head-round (intSystemState st) c3 ≤ Abs.round (vpParent vp))
   PreferredRoundProof {pk}{round₁}{round₂}{bId₁}{bId₂}{v₁abs}{v₂abs}{mbr}{st = post}
                       step@(step-s {pre = pre} r theStep) pkH v₁ v₂ r₁<r₂ refl refl c3
      with msgRound≡ v₁ | msgEpoch≡ v₁ | msgBId≡ v₁
         | msgRound≡ v₂ | msgEpoch≡ v₂ | msgBId≡ v₂
   ...| refl | refl | refl | refl | refl | refl
      with Impl-∈BI? (_vSignature (msgVote v₁)) | Impl-∈BI? (_vSignature (msgVote v₂))
   ...| yes init₁  | yes init₂  = let r₁≡0 = Impl-bsvr (msgSigned v₁) init₁
                                      r₂≡0 = Impl-bsvr (msgSigned v₂) init₂
                                  in ⊥-elim (<⇒≢ r₁<r₂ (trans r₁≡0 (sym r₂≡0)))
   ...| yes init₁  | no  ¬init₂ = let 0≡rv = sym (Impl-bsvr (msgSigned v₁) init₁)
                                      0<rv = v-cand-3-chain⇒0<roundv (intSystemState post) c3
                                  in ⊥-elim (<⇒≢ 0<rv 0≡rv)
   ...| no  ¬init₁ | yes init₂  = let 0≡r₂ = sym (Impl-bsvr (msgSigned v₂) init₂)
                                      r₁   = msgVote v₁ ^∙ vRound
                                  in ⊥-elim (<⇒≱ r₁<r₂ (subst (r₁ ≥_) 0≡r₂ z≤n))
   ...| no  ¬init₁ | no ¬init₂
      with theStep
   ...| step-peer {pid} {st'} {outs} cheat@(step-cheat c) = vpdPres
      where
              m₁sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned v₁) (msg⊆ v₁) (msg∈pool v₁) ¬init₁
              m₂sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned v₂) (msg⊆ v₂) (msg∈pool v₂) ¬init₂
              v₁sb4 = msgSentB4⇒VoteRound∈ (msgSigned v₁) m₁sb4
              v₂sb4 = msgSentB4⇒VoteRound∈ (msgSigned v₂) m₂sb4
              v₁abs' = α-ValidVote-trans {pk} {mbr} {pool = msgPool pre} (msgVote v₁) refl (proj₁ v₁sb4)
              v₂abs' = α-ValidVote-trans {pk} {mbr} {pool = msgPool pre} (msgVote v₂) refl (proj₁ v₂sb4)

              vpdPres : Σ (VoteParentData (intSystemState post) v₂abs)
                          (λ vp → Cand-3-chain-head-round (intSystemState post) c3 ≤ Abs.round (vpParent vp))
              vpdPres
                 with Cand-3-chain-vote-b4 {sp = step-cheat c} pkH r c3 (proj₁ v₁sb4)
              ...| c2' , c2'rnd≡
                 with PreferredRoundProof r pkH (proj₁ v₁sb4) (proj₁ v₂sb4) r₁<r₂ v₁abs' v₂abs' c2'
              ...| vpd , rnd≤
                 with stepPreservesVoteParentData theStep vpd
              ...| res , rnds≡ rewrite sym rnds≡ = res , ≤-trans (≤-reflexive c2'rnd≡) rnd≤
   ...| step-peer (step-honest stP)
      with ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned v₁))
                  (newMsg⊎msgSentB4 r stP pkH (msgSigned v₁) ¬init₁  (msg⊆ v₁) (msg∈pool v₁))
         | ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned v₂))
                  (newMsg⊎msgSentB4 r stP pkH (msgSigned v₂) ¬init₂ (msg⊆ v₂) (msg∈pool v₂))
   ...| inj₂ (v₁sb4 , refl) | inj₂ (v₂sb4 , refl)
        = vpdPres
          where
            v₁abs' = α-ValidVote-trans (msgVote v₁) refl v₁sb4
            v₂abs' = α-ValidVote-trans (msgVote v₂) refl v₂sb4

            vpdPres : _
            vpdPres
               with Cand-3-chain-vote-b4 {sp = step-honest stP} pkH r c3 v₁sb4
            ...| c2' , c2'rnd≡
               with PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs' v₂abs' c2'
            ...| vpd , rnd≤
               with stepPreservesVoteParentData theStep vpd
            ...| res , pars≡ rewrite sym pars≡ =  res , ≤-trans (≤-reflexive c2'rnd≡) rnd≤
   ...| inj₁ (m₁∈outs , v₁pk , newV₁) | inj₁ (m₂∈outs , v₂pk , newV₂) =
              Impl-PR2 r stP pkH (msg⊆ v₁) m₁∈outs (msgSigned v₁) ¬init₁ newV₁ v₁pk (msg⊆ v₂)
                                           m₂∈outs (msgSigned v₂) ¬init₂ newV₂ v₂pk refl r₁<r₂ refl refl c3

   ...| inj₁ (m₁∈outs , v₁pk , v₁New) | inj₂ (v₂sb4 , refl) = help
        where
          round≡ = trans (msgRound≡ v₂sb4) (msgRound≡ v₂)
          ¬bootstrapV₂ = ¬Bootstrap∧Round≡⇒¬Bootstrap step pkH v₂ ¬init₂ (msgSigned v₂sb4) round≡
          epoch≡ = sym (msgEpoch≡ v₂sb4)

          implir0 : _
          implir0 = Impl-IRO r stP pkH (msg⊆ v₁) m₁∈outs (msgSigned v₁) ¬init₁ v₁New v₁pk (msg⊆ v₂sb4)
                                       (msg∈pool v₂sb4)  (msgSigned v₂sb4) ¬bootstrapV₂ epoch≡

          help : _
          help = either (λ r₂<r₁ → ⊥-elim (<⇒≯ r₁<r₂ (<-transʳ (≡⇒≤ (sym round≡)) r₂<r₁)))
                        (λ v₁sb4 → let v₁abs = α-ValidVote-trans (msgVote v₁) refl v₁sb4
                                       v₂abs = α-ValidVote-trans (msgVote v₂) refl v₂sb4
                                       c2'p  = Cand-3-chain-vote-b4 {sp = step-honest stP} pkH r c3 v₁sb4
                                       prp   = PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs v₂abs (proj₁ c2'p)
                                       vpd'  = stepPreservesVoteParentData theStep (proj₁ prp)
                                   in (proj₁ vpd') , (≤-trans (≤-reflexive (proj₂ c2'p)) (proj₂ prp)))
                        implir0
   ...| inj₂ (v₁sb4 , refl)           | inj₁ (m₂∈outs , v₂pk , _) = help
        where
          rv₁<r₂ = <-transʳ (≡⇒≤ (msgRound≡ v₁sb4)) r₁<r₂
          round≡ = trans (msgRound≡ v₁sb4) (msgRound≡ v₁)
          ¬bootstrapV₁ = ¬Bootstrap∧Round≡⇒¬Bootstrap step pkH v₁ ¬init₁ (msgSigned v₁sb4) round≡
          v₁abs' = α-ValidVote-trans (msgVote v₁) refl v₁sb4

          c2'p   = Cand-3-chain-vote-b4 {sp = step-honest stP} pkH r c3 v₁sb4

          implir1 : _
          implir1 = Impl-PR1 r stP pkH (msg⊆ v₂) m₂∈outs (msgSigned v₂) ¬init₂ v₂pk
                                   (msg⊆ v₁sb4) (msg∈pool v₁sb4) (msgSigned v₁sb4) ¬bootstrapV₁
                                   (msgEpoch≡ v₁sb4) rv₁<r₂ v₁abs' refl c3

          help : _
          help = either id
                        (λ v₂sb4 → let v₂abs' = α-ValidVote-trans (msgVote v₂) refl v₂sb4
                                       prp    = PreferredRoundProof r pkH v₁sb4 v₂sb4 r₁<r₂ v₁abs' v₂abs' (proj₁ c2'p)
                                       vpd'   = stepPreservesVoteParentData theStep (proj₁ prp)
                                   in (proj₁ vpd') , (≤-trans (≤-reflexive (proj₂ c2'p)) (proj₂ prp)))
                        implir1

   prr : Type (intSystemState st)
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
