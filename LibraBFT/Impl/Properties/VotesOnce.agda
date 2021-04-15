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

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor.Properties  sha256 sha256-cr
open import LibraBFT.Impl.Handle                                          sha256 sha256-cr
open import LibraBFT.Impl.Handle.Properties                               sha256 sha256-cr
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Properties.Aux
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-EventProcessorAndMeta ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        WithSPS impl-sps-avp
open        Structural impl-sps-avp
open import LibraBFT.Abstract.Util.AvailableEpochs NodeId ℓ-EC EpochConfig EpochConfig.epochId

-- In this module, we prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tackle more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  -- TODO-1: It seems that vo₂ should be proved via a couple of invocations of this property;
  -- the proofs are quite similar.
  newVoteSameEpochGreaterRound : ∀ {pre : SystemState}{pid initd' s' outs v m pk}
                               → ReachableSystemState pre
                               → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) initd' (s' , outs)
                               → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                               → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                               → (v ^∙ vEpoch) ≡ (₋epamEC (peerStates pre pid)) ^∙ epEpoch
                               × suc ((₋epamEC (peerStates pre pid)) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                               × (v ^∙ vRound) ≡ ((₋epamEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote
  newVoteSameEpochGreaterRound _ (step-init _) v⊂m m∈outs sig = ⊥-elim (¬Any[] m∈outs)
  newVoteSameEpochGreaterRound {pre = pre} {pid} {m = m} r (step-msg {(_ , nm)} msg∈pool pinit) v⊂m m∈outs sig vnew
     rewrite pinit
     with nm
  ...| P msg
    with msgsToSendWereSent {pid} {0} {P msg} {m} {peerStates pre pid} m∈outs
  ...| vm , refl , vmSent
    with msgsToSendWereSent1 {pid} {0} {msg} {vm} {peerStates pre pid} vmSent
  ...| _ , v∈outs
     rewrite SendVote-inj-v  (Any-singleton⁻ v∈outs)
           | SendVote-inj-si (Any-singleton⁻ v∈outs)
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {msg} {peerStates pre pid} {vm} v∈outs
     = ⊥-elim (vnew (qcVotesSentB4 r pinit refl qc∈m refl vs∈qc))
  ...| vote∈vm {si} = refl , refl , refl

  -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
  lastVoteRound-mono : ∀ {pre : SystemState}{pid}{initd' ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre initd' (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → (₋epamEC ppre) ^∙ epEpoch ≡ (₋epamEC ppost) ^∙ epEpoch
                     → (₋epamEC ppre) ^∙ epLastVotedRound ≤ (₋epamEC ppost) ^∙ epLastVotedRound
  lastVoteRound-mono _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  lastVoteRound-mono _ ppre≡ (step-msg {(_ , m)} _ _) _
     with m
  ...| P p = const (≤-step (≤-reflexive refl))
  ...| V v = const (≤-reflexive refl)
  ...| C c = const (≤-reflexive refl)

  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.
  LvrProp : CarrierProp
  LvrProp v ep = (  v ^∙ vEpoch ≢ (₋epamEC ep) ^∙ epEpoch
                 ⊎ (v ^∙ vEpoch ≡ (₋epamEC ep) ^∙ epEpoch × v ^∙ vRound ≤ (₋epamEC ep) ^∙ epLastVotedRound))

  LvrCarrier = PropCarrier LvrProp

  firstSendEstablishes : Vote → PK → (origSt : SystemState) → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-peer (step-cheat _ _)) = Lift (ℓ+1 ℓ-EventProcessorAndMeta) ⊥
  firstSendEstablishes   v' pk origSt sysStep@(step-peer {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × LvrCarrier pk (₋vSignature v') (StepPeer-post pstep)   -- <------ Make it record that msgSender (carrSent lvr carriers ≡ ?...
                                                                                  -- <------ or was this the thing I decided to do after the  "rewind"
                         )
  open PeerCanSignForPK

  isValidNewPart⇒fSE : ∀ {pk v'}{pre : SystemState} {post : SystemState} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → (ivnp : IsValidNewPart (₋vSignature v') pk theStep)
                     → firstSendEstablishes v' pk pre theStep
  isValidNewPart⇒fSE {pre = pre} {theStep = step-peer {pid = β} {outs = outs} pstep} hpk (_ , ¬sentb4 , mws , _)
     with Any-++⁻ (List-map (β ,_) outs) (msg∈pool mws)
     -- TODO-1 : Much of this proof is not specific to the particular property being proved, and could be
     -- refactored into Yasm.Properties.  See proof of unwind and refactor to avoid redundancy?
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
     with pstep
  ...| step-cheat fm isCheat
     with thisStep
  ...| here refl
     with isCheat (msg⊆ mws) (msgSigned mws)
  ...| inj₁ dis = ⊥-elim (hpk dis)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)

  isValidNewPart⇒fSE {pk = pk}{pre = pre}{theStep = step-peer {β} {postst} {outs} {.pre} pstep} hpk (r , ¬sentb4 , mws , refl , zefl , vpk)
     | inj₁ thisStep
     | step-honest {.β} {postst} {outs} {init'} hstep
     with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs
     with hstep
  ...| step-init _                   = ⊥-elim (¬Any[] nm∈outs) -- So far these handlers don't send any messages
  ...| step-msg {_ , C _} m∈pool ini = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {_ , V _} m∈pool ini = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {_ , P m} m∈pool ini
     with impl-sps-avp {m = msgWhole mws} r hpk hstep nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ (vpk' , _)
     with noEpochIdChangeYet {ppre = peerStates pre β} r refl hstep ini
  ...| eids≡
     with newVoteSameEpochGreaterRound r hstep (msg⊆ mws) nm∈outs (msgSigned mws)
                                       (subst (λ sig → ¬ MsgWithSig∈ pk sig (msgPool pre))
                                              (sym (msgSameSig mws))
                                              ¬sentb4)
  ...| refl , refl , newlvr
     with StepPeer-post-lemma pstep
  ...| post≡ = r , ¬sentb4 , mkCarrier (step-s r (step-peer (step-honest hstep)))
                                       mws
                                       (override-target-≡ {a = β})
                                       (override-elim-ValidSenderForPK vpk')
                                       (inj₂ ( trans eids≡ (auxEid post≡)
                                             , ≤-reflexive (trans newlvr (auxLvr post≡))))
                                             where auxEid = cong (_^∙ epEpoch ∘ ₋epamEC)
                                                   auxLvr = cong (_^∙ epLastVotedRound ∘ ₋epamEC)

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
     with (msgPart (carrSent prop)) ^∙ vEpoch ≟ (₋epamEC (peerStates pre (msgSender (carrSent prop)))) ^∙ epEpoch
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
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁ r (step-init _) _ _ m∈outs = ⊥-elim (¬Any[] m∈outs)
  vo₁ {pid} {pk = pk} {pre = pre} r sm@(step-msg {(_ , P pm)} m∈pool pidini)  -- Note that only the proposal handler sends messages so far
      {m = m} {v'} hpk v⊂m m∈outs sig ¬sentb4 vpb v'⊂m' m'∈pool sig' refl rnds≡
     with newVoteSameEpochGreaterRound r (step-msg m∈pool pidini) v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the poststate of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of the peer that
     -- sent v'
     with Any-Step-elim {Q = LvrCarrier pk (₋vSignature v') pre}
                        (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE {v' = v'} hpk ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| mkCarrier r' mws ini vpf' preprop
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with sameHonestSig⇒sameVoteData hpk (msgSigned mws) sig' (msgSameSig mws)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre r hb)
  ...| inj₂ refl
     with msgSender mws ≟NodeId pid
  ...| no neq
     -- TODO-2: this will be common, streamline it!
     with msgsToSendWereSent {pid} {0} {P pm} {m} {peerStates pre pid} m∈outs
  ...| vm , refl , send∈
     with msgsToSendWereSent1 {pid} {0} {pm} {vm} {peerStates pre pid} send∈
  ...| recips , SendVote∈
     with voteForCurrentEpoch {0} {pm} {peerStates pre pid} {vm} {recips} SendVote∈
  ...| yyy
     -- We know that *after* the step, pid can sign v (vpb is about pid's post-state).  For v', we
     -- know it about the peerState of (msgSender carrSent) in state "pre".
     with availEpochsConsistent {pid} {msgSender mws} r (inPost pidini sm vpb) (inPre ini vpf')
  ...| 𝓔s≡ = ⊥-elim (neq (trans (trans (sym (nid≡ vpf'))
                                        (PK-inj-same-ECs (sym 𝓔s≡) (trans (pk≡ vpf')
                                                              (sym (pk≡ vpb)))))
                                 (nid≡ vpb)))

  vo₁ {pid} {pk = pk} {pre = pre} r sm@(step-msg m∈pool ps≡)
      {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 vpb v'⊂m' m'∈pool sig' refl rnds≡
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
  vo₂ _ (step-init _) _ _ m∈outs _ _ _ _ _ _ _ _ = ⊥-elim (¬Any[] m∈outs)
  vo₂ {pid = pid} {pre = pre} r (step-msg {_ , nm} _ pinit) {m = m} {m' = m'}
      hpk v⊂m m∈outs sig vnew vpk v'⊂m' m'∈outs sig' v'new vpk' es≡ rnds≡
    with nm
  ...| P msg
    with msgsToSendWereSent {pid} {0} {P msg} {m} {peerStates pre pid} m∈outs
  ...| vm , refl , vmSent
    with msgsToSendWereSent1 {pid} {0} {msg} {vm} {peerStates pre pid} vmSent
  ...| _ , v∈outs
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {msg} {peerStates pre pid} {vm} v∈outs
                        | SendVote-inj-v (Any-singleton⁻ v∈outs)
     = ⊥-elim (vnew (qcVotesSentB4 r pinit refl qc∈m refl vs∈qc))
  ...| vote∈vm {si}
     with m'
  ...| P _ = ⊥-elim (P≢V (Any-singleton⁻ m'∈outs))
  ...| C _ = ⊥-elim (C≢V (Any-singleton⁻ m'∈outs))
  ...| V vm'
       -- Because the handler sends only one message, the two VoteMsgs vm and vm' are the same
     rewrite V-inj (trans (Any-singleton⁻ m'∈outs) (sym (Any-singleton⁻ m∈outs)))
     with v'⊂m'
       -- Both votes are the vote in the (single) VoteMsg, so their biIds must be the same
  ...| vote∈vm = refl
       -- Here we use the same reasoning as above to show that v' is not new
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {msg} {peerStates pre pid} {vm} v∈outs
     = ⊥-elim (v'new (qcVotesSentB4 r pinit refl qc∈m refl vs∈qc))
