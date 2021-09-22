{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        EpochConfig
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
open import Optics.All

-- This module contains definitions and proofs used by both the VotesOnce and PreferredRoundRule
-- proofs.

module LibraBFT.Concrete.Properties.Common (iiah : SystemInitAndHandlers ℓ-RoundManager ConcSysParms) (𝓔 : EpochConfig) where
 open        SystemTypeParameters ConcSysParms
 open        SystemInitAndHandlers iiah
 open        ParamsWithInitAndHandlers iiah
 open import LibraBFT.ImplShared.Util.HashCollisions iiah
 open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms iiah PeerCanSignForPK
                                (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

 record VoteForRound∈ (pk : PK)(round : ℕ)(epoch : ℕ)(bId : HashValue)(pool : SentMessages) : Set where
   constructor mkVoteForRound∈
   field
     msgWhole  : NetworkMsg
     msgVote   : Vote
     msg⊆      : msgVote ⊂Msg msgWhole
     msgSender : ℕ
     msg∈pool  : (msgSender , msgWhole) ∈ pool
     msgSigned : WithVerSig pk msgVote
     msgEpoch≡ : msgVote ^∙ vEpoch ≡ epoch
     msgRound≡ : msgVote ^∙ vRound ≡ round
     msgBId≡   : msgVote ^∙ vProposedId ≡ bId
 open VoteForRound∈ public

 ImplObl-genVotesRound≡0 : Set
 ImplObl-genVotesRound≡0 = ∀ {pk v}
                         → (wvs : WithVerSig pk v)
                         → ∈GenInfo genInfo (ver-signature wvs)
                         → v ^∙ vRound ≡ 0

 ImplObl-genVotesConsistent : Set
 ImplObl-genVotesConsistent = (v1 v2 : Vote)
                             → ∈GenInfo genInfo (_vSignature v1) → ∈GenInfo genInfo (_vSignature v2)
                             → v1 ^∙ vProposedId ≡ v2 ^∙ vProposedId

 ImplObl-NewVoteRound≢0 : Set (ℓ+1 ℓ-RoundManager)
 ImplObl-NewVoteRound≢0 =
   ∀{pid s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (just (s' , outs)))
   → ∀{v m} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v ⊂Msg m → send m ∈ outs
   → (wvs : WithVerSig pk v)
   → (¬ ∈GenInfo genInfo (ver-signature wvs))
   → v ^∙ vRound ≢ 0

 IncreasingRoundObligation : Set (ℓ+1 ℓ-RoundManager)
 IncreasingRoundObligation =
   ∀{pid pid' s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (just (s' , outs)))
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo genInfo (ver-signature sig))
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v pid pk
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre)
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo genInfo (ver-signature sig'))
   -- If v and v' share the same epoch
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v' ^∙ vRound < v ^∙ vRound
     ⊎ VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)

 module ConcreteCommonProperties
        (st         : SystemState)
        (r          : ReachableSystemState st)
        (sps-corr   : StepPeerState-AllValidParts)
        (Impl-gvr   : ImplObl-genVotesRound≡0)
        (Impl-nvr≢0 : ImplObl-NewVoteRound≢0)
   where

   open Structural sps-corr
   open PerReachableState r

   msgSentB4⇒VoteRound∈ : ∀ {v pk pool}
                         → (vv : WithVerSig pk v)
                         → (m : MsgWithSig∈ pk (ver-signature vv) pool)
                         → VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) pool
   msgSentB4⇒VoteRound∈ {v} vv m
       with sameSig⇒sameVoteDataNoCol (msgSigned m) vv (msgSameSig m)
   ...| refl = mkVoteForRound∈ (msgWhole m) (msgPart m) (msg⊆ m) (msgSender m)
                                (msg∈pool m) (msgSigned m) refl refl refl

    -- If a Vote signed for an honest PK has been sent, and it is not in genInfo, then
    -- it is for a round > 0
   NewVoteRound≢0 : ∀ {pk round epoch bId} {st : SystemState}
                     → ReachableSystemState st
                     → Meta-Honest-PK pk
                     → (v : VoteForRound∈ pk round epoch bId (msgPool st))
                     → ¬ ∈GenInfo genInfo (ver-signature (msgSigned v))
                     → round ≢ 0
   NewVoteRound≢0 (step-s r (step-peer (step-honest stP))) pkH v ¬gen r≡0
     with msgRound≡ v
   ...| refl
     with newMsg⊎msgSentB4 r stP pkH (msgSigned v) ¬gen (msg⊆ v) (msg∈pool v)
   ...| Left (m∈outs , _ , _) = ⊥-elim (Impl-nvr≢0 r stP pkH (msg⊆ v) m∈outs
                                                    (msgSigned v) ¬gen r≡0)
   ...| Right m
      with msgSameSig m
   ...| refl
      with sameSig⇒sameVoteDataNoCol (msgSigned m) (msgSigned v) (msgSameSig m)
   ...| refl = let vsb4 = mkVoteForRound∈ (msgWhole m) (msgPart m) (msg⊆ m) (msgSender m)
                                          (msg∈pool m) (msgSigned m) refl refl refl
               in ⊥-elim (NewVoteRound≢0 r pkH vsb4 ¬gen r≡0)
   NewVoteRound≢0 (step-s r (step-peer cheat@(step-cheat c))) pkH v ¬gen r≡0
     with ¬cheatForgeNewSig r cheat unit pkH (msgSigned v) (msg⊆ v) (msg∈pool v) ¬gen
   ...| m
     with msgSameSig m
   ...| refl
      with sameSig⇒sameVoteDataNoCol (msgSigned m) (msgSigned v) (msgSameSig m)
   ...| refl = let vsb4 = mkVoteForRound∈ (msgWhole m) (msgPart m) (msg⊆ m) (msgSender m)
                                       (msg∈pool m) (msgSigned m) refl refl refl
               in ⊥-elim (NewVoteRound≢0 r pkH vsb4 ¬gen (trans (msgRound≡ v) r≡0))


   ¬Gen∧Round≡⇒¬Gen : ∀ {v pk round epoch bId} {st : SystemState}
                     → ReachableSystemState st
                     → Meta-Honest-PK pk
                     → (vfr : VoteForRound∈ pk round epoch bId (msgPool st))
                     → ¬ (∈GenInfo genInfo (ver-signature (msgSigned vfr)))
                     → (sig : WithVerSig pk v)
                     → v ^∙ vRound ≡ round
                     → ¬ (∈GenInfo genInfo (ver-signature sig))
   ¬Gen∧Round≡⇒¬Gen r pkH v₁ ¬genV₁ sigV₂ refl genV₂
     = let v₁r≢0 = NewVoteRound≢0 r pkH v₁ ¬genV₁
       in ⊥-elim (v₁r≢0 (Impl-gvr sigV₂ genV₂))
