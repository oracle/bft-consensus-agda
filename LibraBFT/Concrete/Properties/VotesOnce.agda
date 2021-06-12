{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Base.Types

open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.System
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

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

module LibraBFT.Concrete.Properties.VotesOnce (𝓔 : EpochConfig) where
 -- TODO-3: This may not be the best way to state the implementation obligation.  Why not reduce
 -- this as much as possible before giving the obligation to the implementation?  For example, this
 -- will still require the implementation to deal with hash collisons (v and v' could be different,
 -- but yield the same bytestring and therefore same signature).  Also, avoid the need for the
 -- implementation to reason about messages sent by step-cheat, or give it something to make this
 -- case easy to eliminate.
{-
 record VoteForRound∈ (v : Vote)(pk : PK)(round : ℕ)(epoch : ℕ)(pool : SentMessages) : Set where
   constructor mkVoteForRound∈
   field
     msgWhole     : NetworkMsg
     msg⊆         : v ⊂Msg msgWhole
     msgSender    : ℕ
     msg∈pool     : (msgSender , msgWhole) ∈ pool
     msgSigned    : WithVerSig pk v
     msgSameEpoch : v ^∙ vEpoch ≡ epoch
     msgSameRound : v ^∙ vRound ≡ round
 open VoteForRound∈ public
-}


 record VoteForRound∈ (pk : PK)(round : ℕ)(epoch : ℕ)(bId : HashValue)(pool : SentMessages) : Set where
   constructor mkVoteForRound∈
   field
     msgWhole     : NetworkMsg
     msgVote      : Vote
     msg⊆         : msgVote ⊂Msg msgWhole
     msgSender    : ℕ
     msg∈pool     : (msgSender , msgWhole) ∈ pool
     msgSigned    : WithVerSig pk msgVote
     msgSameEpoch : msgVote ^∙ vEpoch ≡ epoch
     msgSameRound : msgVote ^∙ vRound ≡ round
     msgSameBId   : msgVote ^∙ vProposedId ≡ bId
 open VoteForRound∈ public


 NewVoteSignedAndRound>0 : Set (ℓ+1 ℓ-RoundManager)
 NewVoteSignedAndRound>0 =
   ∀{pid s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → ∀{v m} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v ⊂Msg m → send m ∈ outs
   → Σ (WithVerSig pk v) λ sig → (¬ ∈GenInfo (ver-signature sig) → v ^∙ vRound > 0)

 IncreasingRoundObligation : Set (ℓ+1 ℓ-RoundManager)
 IncreasingRoundObligation =
   ∀{pid pid' s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre)
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v' ^∙ vRound < v ^∙ vRound
     ⊎ VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)

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
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound ≡ v' ^∙ vRound
   ----------------------------------------------------------
   -- Then, an honest implemenation promises v and v' vote for the same blockId.
   → v ^∙ vProposedId ≡ v' ^∙ vProposedId

 -- Next, we prove that, given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-VO1 : IncreasingRoundObligation)
   (Impl-VO2 : ImplObligation₂)
   where

  -- Any reachable state satisfies the VO rule for any epoch in the system.
  module _ (st : SystemState)(r : ReachableSystemState st) where

   open Structural sps-corr
   -- Bring in intSystemState
   open PerState st r
   open PerEpoch 𝓔

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

    msbSentB4⇒VoteForRound∈ : ∀ {pk sig msgPool}
                              → (m : MsgWithSig∈ pk sig msgPool)
                              → let v = msgPart m
                                in VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch)
                                                 (v ^∙ vProposedId) msgPool
    msbSentB4⇒VoteForRound∈ m = mkVoteForRound∈ (msgWhole m) (msgPart m) (msg⊆ m) (msgSender m)
                                                (msg∈pool m) (msgSigned m) refl refl refl

    VotesOnceProof :
       ∀ {pk round epoch blockId₁ blockId₂} {st : SystemState}
       → ReachableSystemState st
       → Meta-Honest-PK pk
       → (m₁ : VoteForRound∈ pk round epoch blockId₁ (msgPool st))
       → (m₂ : VoteForRound∈ pk round epoch blockId₂ (msgPool st))
       → blockId₁ ≡ blockId₂
    VotesOnceProof step-0 _ m₁ = ⊥-elim (¬Any[] (msg∈pool m₁))
    VotesOnceProof step@(step-s r theStep) pkH m₁ m₂
       with ∈GenInfo? (₋vSignature (msgVote m₁)) | ∈GenInfo? (₋vSignature (msgVote m₂))
    ...| yes init  | yes init' = let b₁≡b₂ = genVotesConsistent (msgVote m₁) (msgVote m₂)
                                             init init'
                                 in trans (sym (msgSameBId m₁)) (trans b₁≡b₂ (msgSameBId m₂))
    ...| yes init  | no  ¬init = let r₁≡0 = genVotesRound≡0 (msgSigned m₁) init
                                     r₂≢0 = ¬genVotesRound≢0 step pkH (msgSigned m₂)
                                                              (msg⊆ m₂) (msg∈pool m₂) ¬init
                                     r₂≡r₁ = trans (msgSameRound m₂) (sym (msgSameRound m₁))
                                 in ⊥-elim (r₂≢0 (trans r₂≡r₁ r₁≡0))
    ...| no  ¬init | yes init  = let r₁≢0 = ¬genVotesRound≢0 step pkH (msgSigned m₁)
                                                              (msg⊆ m₁) (msg∈pool m₁) ¬init
                                     r₂≡0 = genVotesRound≡0 (msgSigned m₂) init
                                     r₁≡r₂ = trans (msgSameRound m₁) (sym (msgSameRound m₂))
                                 in ⊥-elim (r₁≢0 (trans r₁≡r₂ r₂≡0))
    ...| no  ¬init | no ¬init'
       with theStep
    ...| step-peer cheat@(step-cheat c)
       with ¬cheatForgeNewVote r cheat unit pkH (msgSigned m₁) (msg⊆ m₁) (msg∈pool m₁) ¬init
          | ¬cheatForgeNewVote r cheat unit pkH (msgSigned m₂) (msg⊆ m₂) (msg∈pool m₂) ¬init'
    ...| m₁sb4 | m₂sb4 = let v₁sb4 = msbSentB4⇒VoteForRound∈ {!m₁sb4!}
                             v₂sb4 = {!!}
                         in VotesOnceProof r pkH v₁sb4 v₂sb4
    VotesOnceProof step@(step-s r theStep) pkH m₁ m₂
       | no  ¬init | no ¬init'
       | step-peer (step-honest stPeer) = {!!}

 {-   VotesOnceProof step-0 _ _ msv = ⊥-elim (¬Any[] (msg∈pool msv)) --(msg∈pool msv))
    VotesOnceProof {v} {v'} (step-s r theStep) pkH vv msv vv' msv' eid≡ r≡
       with ∈GenInfo? (₋vSignature (msgPart msv)) | ∈GenInfo? (₋vSignature (msgPart msv'))
    ...| yes init  | yes init' =  genVotesConsistent (msgPart msv) (msgPart msv') init init'
       -- A signature in GenInfo is for a vote with round 0, and a signature for which we have a
       -- MsgWithSig∈ that is not in GenInfo and is for an honest PK is for a round ≢ 0, so we can
       -- derive a contradiction using r≡.
    ...| yes init  | no  ¬init = ⊥-elim (¬genVotesRound≢0 (step-s r theStep) pkH msv' ¬init ((trans (sym r≡) (genVotesRound≡0 vv  init))))
    ...| no  ¬init | yes init  = ⊥-elim (¬genVotesRound≢0 (step-s r theStep) pkH msv  ¬init ((trans r≡       (genVotesRound≡0 vv' init))))
    ...| no  ¬init | no ¬init'
       with theStep
    ...| step-peer cheat@(step-cheat c)
       with ¬cheatForgeNew cheat refl unit pkH msv  ¬init
          | ¬cheatForgeNew cheat refl unit pkH msv' ¬init'
    ...| msb4 | m'sb4
       with  msgSameSig msb4 | msgSameSig m'sb4
    ...| refl | refl = VotesOnceProof r pkH vv msb4 vv' m'sb4 eid≡ r≡

    VotesOnceProof (step-s r theStep) pkH vv msv vv' msv' eid≡ r≡
       | refl | refl
       | refl | refl
       | no  ¬init | no ¬init'
       | step-peer (step-honest stPeer)
       with newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv)  ¬init  (msg⊆ msv)  (msg∈pool msv)
          | newMsg⊎msgSentB4 r stPeer pkH (msgSigned msv') ¬init' (msg⊆ msv') (msg∈pool msv')
    ...| inj₂ msb4                   | inj₂ m'sb4
         = VotesOnceProof r pkH vv msb4 vv' m'sb4 eid≡ r≡
    ...| inj₁ (m∈outs , vspk , newV) | inj₁ (m'∈outs , v'spk , newV')
      = Impl-VO2 r stPeer pkH (msg⊆ msv) m∈outs (msgSigned msv) ¬init newV vspk
                 (msg⊆ msv') m'∈outs (msgSigned msv') ¬init' newV' v'spk eid≡ r≡
    ...| inj₁ (m∈outs , vspk , newV) | inj₂ m'sb4
       with sameSig⇒sameVoteData (msgSigned m'sb4) vv' (msgSameSig m'sb4)
    ...| inj₁ hb   = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl
      = ⊥-elim (<⇒≢ (Impl-VO1 r stPeer pkH (msg⊆ msv) m∈outs (msgSigned msv) ¬init
                               ?
                               (msg⊆ m'sb4) (msg∈pool m'sb4) (msgSigned m'sb4)
                               (¬subst ¬init' (msgSameSig m'sb4)) eid≡)
               (sym r≡))
    VotesOnceProof (step-s r theStep) pkH vv msv vv' msv' eid≡ r≡
       | refl | refl
       | refl | refl
       | no  ¬init | no ¬init'
       | step-peer (step-honest stPeer)
       | inj₂ msb4                   | inj₁ (m'∈outs , v'spk , newV')
       with sameSig⇒sameVoteData (msgSigned msb4) vv (msgSameSig msb4)
    ...| inj₁ hb = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl
      = ⊥-elim (<⇒≢ (Impl-VO1 r stPeer pkH (msg⊆ msv') m'∈outs (msgSigned msv') ¬init'
                              ?
                              (msg⊆ msb4) (msg∈pool msb4) (msgSigned msb4)
                              (¬subst ¬init (msgSameSig msb4)) (sym eid≡))
                r≡)-}

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
