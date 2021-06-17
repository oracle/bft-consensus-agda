{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplFake.Handle
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open        EpochConfig
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
   → let post = StepPeer-post {pre = pre} (step-honest sps) in
     ∀{mbr v vabs m v' v'abs m'}
   -- 𝓔 must be "in the system" after the step
   → (𝓔∈Sys : EpochConfig∈Sys post 𝓔)
   → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre)
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   -- If v and v' share the same epoch
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   -- and v is for a smaller round
   → v ^∙ vRound < v' ^∙ vRound
   -- and mbr is the Member corresponding to the peer taking the steo
   → toNodeId 𝓔 mbr ≡ pid
   -- and vabs* are the abstract Votes for v and v'
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → let intSys = PerState.PerEpoch.intSystemState pre r 𝓔 in
   -- and vabs could contribute to a 3-chain
     (c2 : Cand-3-chain-vote intSys vabs)
   -- then the round of the block that v' votes for is at least the round of
   -- the grandparent of the block that v votes for (i.e., the preferred round rule)
   → Σ (VoteParentData intSys v'abs)
           (λ vp → Cand-3-chain-head-round intSys c2 ≤ Abs.round (vpParent vp))

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
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))

   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
   -- If v and v' share the same epoch
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   -- and v is for a smaller round
   → v ^∙ vRound < v' ^∙ vRound
   → toNodeId 𝓔 mbr ≡ pid
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → let intSys = PerState.PerEpoch.intSystemState pre r 𝓔 in
     (c2 : Cand-3-chain-vote intSys vabs)
   → Σ (VoteParentData intSys v'abs)
           (λ vp → Cand-3-chain-head-round intSys c2
                   ≤ Abs.round (vpParent vp))

 -- Next, we prove that given the necessary obligations, we can prove the type required (by
 -- LibraBFT.Concrete.Obligations.PreferredRound.proof) to prove the type needed by the abstract
 -- proofs for the preferred round rule.
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

   postulate
     prr : PR.Type intSystemState
   -- prr honα refl sv refl sv' c2 round< = {!c2!}
