{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
-- This module proves the two "VotesOnce" proof obligations for our fake handler

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS

import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.Impl.Base.Types

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        WithSPS impl-sps-avp
open        Structural impl-sps-avp

-- In this module, we prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tackle more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.
  LvrProp : CarrierProp
  LvrProp v rm = (  v ^∙ vEpoch ≢ (₋rmEC rm) ^∙ rmEpoch
                 ⊎ (v ^∙ vEpoch ≡ (₋rmEC rm) ^∙ rmEpoch × v ^∙ vRound ≤ (₋rmEC rm) ^∙ rmLastVotedRound))

  LvrCarrier = PropCarrier LvrProp

  firstSendEstablishes : Vote → PK → (origSt : SystemState) → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-peer (step-cheat _)) = Lift (ℓ+1 ℓ-RoundManager) ⊥
  firstSendEstablishes   v' pk origSt sysStep@(step-peer {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × LvrCarrier pk (₋vSignature v') (StepPeer-post pstep)
                         )
  open PeerCanSignForPK

  isValidNewPart⇒fSE : ∀ {pk v'}{pre : SystemState} {post : SystemState} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → (ivnp : IsValidNewPart (₋vSignature v') pk theStep)
                     → firstSendEstablishes v' pk pre theStep
  isValidNewPart⇒fSE {pre = pre} {theStep = step-peer {pid = β} {outs = outs} pstep} hpk (_ , ¬init , ¬sentb4 , mws , _)
     with Any-++⁻ (List-map (β ,_) outs) (msg∈pool mws)
     -- TODO-1 : Much of this proof is not specific to the particular property being proved, and could be
     -- refactored into Yasm.Properties.  See proof of unwind and refactor to avoid redundancy?
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
     with pstep
  ...| step-cheat isCheat
     with thisStep
  ...| here refl
     with isCheat (msg⊆ mws) (msgSigned mws) (transp-¬∈GenInfo₁ ¬init mws)
  ...| inj₁ dis = ⊥-elim (hpk dis)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)

  isValidNewPart⇒fSE {pk}{v'}{pre}{theStep = step-peer {β} {postst} {outs} {.pre} pstep} hpk (r , ¬init , ¬sentb4 , mws , refl , zefl , vpk)
     | inj₁ thisStep
     | step-honest {.β} hstep
     with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs
     with hstep
  ...| step-msg {_ , P m} m∈pool ini
     with impl-sps-avp {m = msgWhole mws} r hpk hstep nm∈outs (msg⊆ mws) (msgSigned mws) (transp-¬∈GenInfo₁ ¬init mws )
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ (vpk' , _)
     with noEpochIdChangeYet {ppre = peerStates pre β} r refl hstep ini
  ...| eids≡
     with newVoteSameEpochGreaterRound r hstep (¬subst ¬init (msgSameSig mws)) hpk (msg⊆ mws) nm∈outs (msgSigned mws)
                                               (¬subst ¬sentb4 (msgSameSig mws))
  ...| refl , refl , newlvr
     with StepPeer-post-lemma pstep
  ...| post≡ = r , ¬sentb4 , mkCarrier (step-s r (step-peer (step-honest hstep)))
                                       mws
                                       (override-target-≡ {a = β})
                                       vpk'
                                       (inj₂ ( trans eids≡ (auxEid post≡)
                                             , ≤-reflexive (trans newlvr (auxLvr post≡))))
                                       where auxEid = cong (_^∙ rmEpoch ∘ ₋rmEC)
                                             auxLvr = cong (_^∙ rmLastVotedRound ∘ ₋rmEC)

  ImplPreservesLvr : PeerStepPreserves LvrProp
  -- We don't have a real model for the initial peer state, so we can't prove this case yet.
  -- Eventually, we'll prove something like a peer doesn't initialize to an epoch for which
  -- it has already sent votes.
  ImplPreservesLvr r prop (step-init uni) = ⊥-elim (uninitd≢initd (trans (sym uni) (carrInitd prop)))
  ImplPreservesLvr {pre = pre} r prop (step-msg {m} m∈pool inited)
     with carrProp prop
  ...| preprop
     with noEpochIdChangeYet r refl (step-msg m∈pool inited) (carrInitd prop)
  ...| eids≡
     with preprop
  ...| inj₁ diffEpoch = inj₁ λ x → diffEpoch (trans x (sym eids≡))
  ...| inj₂ (sameEpoch , rnd≤ppre)
     with (msgPart (carrSent prop)) ^∙ vEpoch ≟ (₋rmEC (peerStates pre (msgSender (carrSent prop)))) ^∙ rmEpoch
  ...| no neq = ⊥-elim (neq sameEpoch)
  ...| yes refl
     with lastVoteRound-mono r refl (step-msg m∈pool inited) (carrInitd prop)
  ...| es≡⇒lvr≤
     = inj₂ (eids≡ , ≤-trans rnd≤ppre (es≡⇒lvr≤ eids≡))

  LvrCarrier-transp* : ∀ {pk sig} {start : SystemState}{final : SystemState}
                     → LvrCarrier pk sig start
                     → (step* : Step* start final)
                     → LvrCarrier pk sig final
  LvrCarrier-transp* lvrc step-0 = lvrc
  LvrCarrier-transp* lvrc (step-s s* s) = Carrier-transp LvrProp ImplPreservesLvr s (LvrCarrier-transp* lvrc s*)

  fSE⇒rnd≤lvr : ∀ {v' pk}
              → {final : SystemState}
              → Meta-Honest-PK pk
              → ∀ {pre : SystemState}{post : SystemState}{theStep : Step pre post}
              → firstSendEstablishes v' pk post theStep
              → Step* post final
              → LvrCarrier pk (signature v' unit) final
  fSE⇒rnd≤lvr hpk {theStep = step-peer (step-honest _)} (_ , _ , lvrc) step* = LvrCarrier-transp* lvrc step*

  vo₁ : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far; Agda figures that out so no proof
  -- required here.  In future it may send messages, but any verifiable Signatures for honest PKs
  -- they contain will be from GenesisInfo.
  vo₁ {pid} {pk = pk} {pre = pre} r sm@(step-msg {(_ , nm)} m∈pool pidini)
      {m = m} {v'} hpk v⊂m m∈outs sig ¬init ¬sentb4 vpb v'⊂m' m'∈pool sig' ¬init' refl rnds≡
     with msgsToSendWereSent {pid} {nm} m∈outs
  ...| _ , vm , _ , refl , _
     with newVoteSameEpochGreaterRound r (step-msg m∈pool pidini) ¬init hpk v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the poststate of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of the peer that
     -- sent v'
     with Any-Step-elim {Q = LvrCarrier pk (₋vSignature v') pre}
                        (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-map (λ _ ivnp → isValidNewPart⇒fSE {v' = v'} hpk ivnp)
                                      (unwind r hpk v'⊂m' m'∈pool sig' ¬init'))
  ...| mkCarrier r' mws ini vpf' preprop
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with sameSig⇒sameVoteData (msgSigned mws) sig' (msgSameSig mws)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre r hb)
  ...| inj₂ refl
     with msgSender mws ≟NodeId pid
  ...| no neq =
     -- We know that *after* the step, pid can sign v (vpb is about the post-state).  For v', we
     -- know it about state "pre"; we transport this to the post-state using
     -- PeerCanSignForPK-Stable.  Because EpochConfigs known in a system state are consistent with
     -- each other (i.e., trivially, for now because only the initial EpochConfig is known), we can
     -- use PK-inj to contradict the assumption that v and v' were sent by different peers (neq).
     let theStep = step-peer (step-honest sm)
         vpf''   = PeerCanSignForPK-stable r theStep vpf'
         𝓔s≡     = availEpochsConsistent {pid} {msgSender mws} (step-s r theStep) vpb vpf''
     in  ⊥-elim (neq (trans (trans (sym (nid≡ vpf''))
                                   (PK-inj-same-ECs (sym 𝓔s≡)
                                                    (trans (pk≡ vpf'') (sym (pk≡ vpb)))))
                            (nid≡ vpb)))

  vo₁ {pid} {pk = pk} {pre = pre} r sm@(step-msg m∈pool ps≡)
      {v' = v'} hpk v⊂m m∈outs sig ¬init ¬sentb4 vpb v'⊂m' m'∈pool sig' _ refl rnds≡
     | _ , vm , _ , refl , _
     | eIds≡' , suclvr≡v'rnd , _
     | mkCarrier r' mws ini vpf' preprop
     | inj₂ refl
     | yes refl
     with preprop
  ...| inj₁ diffEpoch = ⊥-elim (diffEpoch eIds≡')
  ...| inj₂ (sameEpoch , v'rnd≤lvr)
                    -- So we have proved both that the round of v' is ≤ the lastVotedRound of
                    -- the peer's state and that the round of v' is one greater than that value,
                    -- which leads to a contradiction
                    = ⊥-elim (1+n≰n (≤-trans (≤-reflexive suclvr≡v'rnd)
                                             (≤-trans (≤-reflexive rnds≡) v'rnd≤lvr)))

  -- TODO-1: This proof should be refactored to reduce redundant reasoning about the two votes.  The
  -- newVoteSameEpochGreaterRound property uses similar reasoning.

  vo₂ : VO.ImplObligation₂
  vo₂ {pid = pid} {pk = pk} {pre = pre} r (step-msg {_ , nm} m∈pool pinit) {v = v} {m}
      hpk v⊂m m∈outs sig ¬init vnew vpk v'⊂m' m'∈outs sig' ¬init' v'new vpk' es≡ rnds≡
     with msgsToSendWereSent {pid} {nm} m∈outs
  ...| _ , vm , pm , refl , refl
    with proposalHandlerSentVote {pid} {0} {pm} {vm} {peerStates pre pid} m∈outs
  ...| _ , v∈outs
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {pm} {peerStates pre pid} {vm} v∈outs
                        | SendVote-inj-v (Any-singleton⁻ v∈outs)
     with qcVotesSentB4 r pinit
                        (VoteMsgQCsFromRoundManager r (step-msg m∈pool pinit) hpk v⊂m m∈outs qc∈m) vs∈qc ¬init
  ...| mws = ⊥-elim (vnew mws)

  vo₂ {pid = pid} {pk = pk} {pre = pre} r (step-msg {_ , nm} m∈pool pinit) {v = v} {m} {v'} {m'}
      hpk v⊂m m∈outs sig ¬init vnew vpk v'⊂m' m'∈outs sig' ¬init' v'new vpk' es≡ rnds≡
     | _ , vm , pm , refl , refl
     | _ , v∈outs
     | vote∈vm
     with msgsToSendWereSent {pid} {nm} {m'} {st = peerStates pre pid} m'∈outs
  ...| _ , vm' , pm , refl , refl
    with proposalHandlerSentVote {pid} {0} {pm} {vm'} {peerStates pre pid} m'∈outs
  ...| _ , v'∈outs
       rewrite cong ₋vmVote (SendVote-inj-v (trans (Any-singleton⁻ v∈outs) (sym (Any-singleton⁻ v'∈outs))))
    with v'⊂m'
  ...| vote∈vm = refl
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {pm} {peerStates pre pid} {vm} v∈outs
                        | SendVote-inj-v (Any-singleton⁻ v∈outs)
                        | cong ₋vmVote (SendVote-inj-v (trans (Any-singleton⁻ v∈outs) (sym (Any-singleton⁻ v'∈outs))))
    with qcVotesSentB4 r pinit
                       (VoteMsgQCsFromRoundManager r (step-msg m∈pool pinit) hpk v'⊂m' m'∈outs qc∈m) vs∈qc ¬init'
  ...| mws = ⊥-elim (v'new mws)
