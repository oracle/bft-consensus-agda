{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
open import Optics.All

open        EpochConfig

-- In this module, we define two "implementation obligations"
-- (ImplObligationᵢ for i ∈ {1 , 2}), which are predicates over
-- reachable states of a system defined by
-- 'LibraBFT.Concrete.System.Parameters'.  These two properties relate
-- votes sent by the same sender, ensuring that if they are for the
-- same epoch and round, then they vote for the same blockID; the
-- first relates a vote output by the handler to a vote sent
-- previously, and the second relates two votes both sent by the
-- handler.
--
-- We then prove that, if an implementation satisfies these two
-- semantic obligations, along with a structural one about messages
-- sent by honest peers in the implementation, then the implemenation
-- satisfies the LibraBFT.Abstract.Properties.VotesOnce invariant.

-- It is not actually necessary to provide an EpochConfig to define
-- these implementation obligations, but it is needed below to state
-- the goal of the proof (voo).  In contrast, the PreferredRound rule
-- requires and EpochConfig to state the obligations, because they
-- are defined in terms of abstract Records, which are defined for an
-- EpochConfig.  We introduce the EpochConfig at the top of this
-- module for consistency with the PreferredRound rule so that the
-- order of parameters to invoke the respective proofs is consistent.
module LibraBFT.Concrete.Properties.VotesOnce (iiah : SystemInitAndHandlers ℓ-RoundManager ConcSysParms) (𝓔 : EpochConfig) where
 open        SystemTypeParameters ConcSysParms
 open        SystemInitAndHandlers iiah
 open        ParamsWithInitAndHandlers iiah
 open import LibraBFT.ImplShared.Util.HashCollisions iiah
 open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms iiah PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
 open import LibraBFT.Concrete.Properties.Common iiah 𝓔


 -- TODO-3: This may not be the best way to state the implementation obligation.  Why not reduce
 -- this as much as possible before giving the obligation to the implementation?  For example, this
 -- will still require the implementation to deal with hash collisons (v and v' could be different,
 -- but yield the same bytestring and therefore same signature).  Also, avoid the need for the
 -- implementation to reason about messages sent by step-cheat, or give it something to make this
 -- case easy to eliminate.

 ImplObligation₂ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₂ =
   ∀{pid s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → ∀{v m v' m'}
   → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo genInfo (ver-signature sig))
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v pid pk
   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo genInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
   → PeerCanSignForPK (StepPeer-post {pre = pre} (step-honest sps)) v' pid pk
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound ≡ v' ^∙ vRound
   ----------------------------------------------------------
   -- Then, an honest implemenation promises v and v' vote for the same blockId.
   → v ^∙ vProposedId ≡ v' ^∙ vProposedId

 -- Next, we prove that, given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-gvc : ImplObl-genVotesConsistent)
   (Impl-gvr : ImplObl-genVotesRound≡0)
   (Impl-v≢0 : ImplObl-NewVoteSignedAndRound≢0)
   (Impl-∈GI? : (sig : Signature) → Dec (∈GenInfo genInfo sig))
   (Impl-IRO : IncreasingRoundObligation)
   (Impl-VO2 : ImplObligation₂)
   where

  -- Any reachable state satisfies the VO rule for any epoch in the system.
  module _ (st : SystemState)(r : ReachableSystemState st) where

   open Structural sps-corr
   -- Bring in intSystemState
   open PerState st
   open PerReachableState r
   open PerEpoch 𝓔
   open ConcreteCommonProperties st r Impl-gvr

   open import LibraBFT.Concrete.Obligations.VotesOnce 𝓔 (ConcreteVoteEvidence 𝓔) as VO

   -- The VO proof is done by induction on the execution trace leading to 'st'. In
   -- Agda, this is 'r : RechableSystemState st' above.

   private

    -- From this point onwards, it might be easier to read this proof starting at 'voo'
    -- at the end of the file. Next, we provide an overview the proof.
    --
    -- We wish to prove that, for any two votes v and v' cast by an honest α in the message
    -- pool of a state st, if v and v' have equal rounds and epochs, then they vote for the
    -- same block.
    --
    -- The base case and the case for a new epoch in the system are trivial. For the base case
    -- we get to a contradiction because it's not possible to have any message in the msgpool.
    --
    -- Regarding the PeerStep case. The induction hypothesis tells us that the property holds
    -- in the pre-state.  Next, we reason about the post-state.  We start by analyzing whether
    -- v and v' have been sent as outputs of the PeerStep under scrutiny or were already in
    -- the pool before.
    --
    -- There are four possibilities:
    --
    --   i) v and v' were aleady present in the msgPool before: use induction hypothesis.
    --  ii) v and v' are both in the output produced by the PeerStep under scrutiny.
    -- iii) v was present before, but v' is new.
    --  iv) v' was present before, but v is new.
    --
    -- In order to obtain this four possiblities we invoke newMsg⊎msgSent4 lemma, which
    -- receives proof that some vote is in a message that is in the msgPool of the post state
    -- and returns evidence that either the vote is new or that some message with the same
    -- signature was sent before.
    --
    -- Case (i) is trivial; cases (iii) and (iv) are symmetric and reduce to an implementation
    -- obligation (Impl-VO1) and case (ii) reduces to a different implementation obligation
    -- (Impl-VO2).

    VotesOnceProof :
       ∀ {pk round epoch blockId₁ blockId₂} {st : SystemState}
       → ReachableSystemState st
       → Meta-Honest-PK pk
       → (m₁ : VoteForRound∈ pk round epoch blockId₁ (msgPool st))
       → (m₂ : VoteForRound∈ pk round epoch blockId₂ (msgPool st))
       → blockId₁ ≡ blockId₂
    VotesOnceProof step-0 _ m₁ = ⊥-elim (¬Any[] (msg∈pool m₁))
    VotesOnceProof step@(step-s r theStep) pkH m₁ m₂
       with msgRound≡ m₁ | msgEpoch≡ m₁ | msgBId≡ m₁
          | msgRound≡ m₂ | msgEpoch≡ m₂ | msgBId≡ m₂
    ...| refl | refl | refl | refl | refl | refl
       with Impl-∈GI? (_vSignature (msgVote m₁)) | Impl-∈GI? (_vSignature (msgVote m₂))
    ...| yes init₁  | yes init₂  = Impl-gvc (msgVote m₁) (msgVote m₂) init₁ init₂
    ...| yes init₁  | no  ¬init₂ = ⊥-elim (NewVoteRound≢0 step pkH m₂ ¬init₂ (Impl-gvr (msgSigned m₁) init₁))
    ...| no  ¬init₁ | yes init₂  = ⊥-elim (NewVoteRound≢0 step pkH m₁ ¬init₁ (Impl-gvr (msgSigned m₂) init₂))
    ...| no  ¬init₁ | no ¬init₂
       with theStep
    ...| step-peer cheat@(step-cheat c)
         = let m₁sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned m₁) (msg⊆ m₁) (msg∈pool m₁) ¬init₁
               m₂sb4 = ¬cheatForgeNewSig r cheat unit pkH (msgSigned m₂) (msg⊆ m₂) (msg∈pool m₂) ¬init₂
               v₁sb4 = msgSentB4⇒VoteRound∈ (msgSigned m₁) m₁sb4
               v₂sb4 = msgSentB4⇒VoteRound∈ (msgSigned m₂) m₂sb4
           in VotesOnceProof r pkH v₁sb4 v₂sb4
    ...| step-peer (step-honest stP)
       with ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned m₁))
                   (newMsg⊎msgSentB4 r stP pkH (msgSigned m₁) ¬init₁  (msg⊆ m₁) (msg∈pool m₁))
          | ⊎-map₂ (msgSentB4⇒VoteRound∈ (msgSigned m₂))
                   (newMsg⊎msgSentB4 r stP pkH (msgSigned m₂) ¬init₂ (msg⊆ m₂) (msg∈pool m₂))
    ...| inj₂ v₁sb4                | inj₂ v₂sb4
         = VotesOnceProof r pkH v₁sb4 v₂sb4
    ...| inj₁ (m₁∈outs , v₁pk , v₁New) | inj₁ (m₂∈outs , v₂pk , v₂New)
         = Impl-VO2 r stP pkH (msg⊆ m₁) m₁∈outs (msgSigned m₁) ¬init₁ v₁New v₁pk
                    (msg⊆ m₂) m₂∈outs (msgSigned m₂) ¬init₂ v₂New v₂pk refl refl
    ...| inj₁ (m₁∈outs , v₁pk , v₁New) | inj₂ v₂sb4
         = let round≡ = trans (msgRound≡ v₂sb4) (msgRound≡ m₂)
               ¬genV₂ = ¬Gen∧Round≡⇒¬Gen step pkH m₂ ¬init₂ (msgSigned v₂sb4) round≡
               epoch≡ = sym (msgEpoch≡ v₂sb4)
           in either (λ v₂<v₁ → ⊥-elim (<⇒≢ v₂<v₁ (msgRound≡ v₂sb4)))
                     (λ v₁sb4 → VotesOnceProof r pkH v₁sb4 v₂sb4)
                     (Impl-IRO r stP pkH (msg⊆ m₁) m₁∈outs (msgSigned m₁) ¬init₁ v₁New v₁pk
                               (msg⊆ v₂sb4) (msg∈pool v₂sb4) (msgSigned v₂sb4) ¬genV₂ epoch≡)
    ...| inj₂ v₁sb4                | inj₁ (m₂∈outs , v₂pk , v₂New)
         = let round≡ = trans (msgRound≡ v₁sb4) (msgRound≡ m₁)
               ¬genV₁ = ¬Gen∧Round≡⇒¬Gen step pkH m₁ ¬init₁ (msgSigned v₁sb4) round≡
           in either (λ v₁<v₂ → ⊥-elim (<⇒≢ v₁<v₂ (msgRound≡ v₁sb4)))
                     (λ v₂sb4 → VotesOnceProof r pkH v₁sb4 v₂sb4)
                     (Impl-IRO r stP pkH (msg⊆ m₂) m₂∈outs (msgSigned m₂) ¬init₂ v₂New v₂pk
                               (msg⊆ v₁sb4) (msg∈pool v₁sb4) (msgSigned v₁sb4) ¬genV₁
                               (sym (msgEpoch≡ v₁sb4)))


   voo : VO.Type intSystemState
   voo hpk refl sv refl sv' refl
      with vmsg≈v (vmFor sv) | vmsg≈v (vmFor sv')
   ...| refl | refl
      with vmsgEpoch (vmFor sv) | vmsgEpoch (vmFor sv')
   ...| refl | refl
       = let vfr  = mkVoteForRound∈ (nm (vmFor sv)) (cv ((vmFor sv))) (cv∈nm (vmFor sv))
                                    (vmSender sv) (nmSentByAuth sv) (vmsgSigned (vmFor sv))
                                    (vmsgEpoch (vmFor sv)) refl refl
             vfr' = mkVoteForRound∈ (nm (vmFor sv')) (cv (vmFor sv')) (cv∈nm (vmFor sv'))
                                    (vmSender sv') (nmSentByAuth sv') (vmsgSigned (vmFor sv'))
                                    (vmsgEpoch (vmFor sv')) refl refl
         in VotesOnceProof r hpk vfr vfr'
