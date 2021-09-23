{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
-- This module proves the two "VotesOnce" proof obligations for our fake handler

{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.ImplFake.Consensus.RoundManager.Properties
open import LibraBFT.ImplFake.Handle
open import LibraBFT.ImplFake.Handle.Properties
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
open import Optics.All

open        ParamsWithInitAndHandlers FakeInitAndHandlers
import      LibraBFT.Concrete.Properties.Common FakeInitAndHandlers as Common
import      LibraBFT.Concrete.Properties.VotesOnce FakeInitAndHandlers as VO
open import LibraBFT.ImplShared.Util.HashCollisions FakeInitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms FakeInitAndHandlers
                               PeerCanSignForPK PeerCanSignForPK-stable

-- In this module, we prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tackle more
-- ambitious properties.


module LibraBFT.ImplFake.Properties.VotesOnce (𝓔 : EpochConfig) where
  open        Structural impl-sps-avp

  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.
  LvrProp : CarrierProp
  LvrProp v rm = (  v ^∙ vEpoch ≢ rm ^∙ rmEpoch
                 ⊎ (v ^∙ vEpoch ≡ rm ^∙ rmEpoch × v ^∙ vRound ≤ rm ^∙ rmLastVotedRound))

  LvrCarrier = PropCarrier LvrProp

  firstSendEstablishes : Vote → PK → (origSt : SystemState) → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-peer (step-cheat _)) = Lift (ℓ+1 ℓ-RoundManager) ⊥
  firstSendEstablishes   v' pk origSt sysStep@(step-peer {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × LvrCarrier pk (_vSignature v') (StepPeer-post pstep)
                         )
  open PeerCanSignForPK
  open PeerCanSignForPKinEpoch

  isValidNewPart⇒fSE : ∀ {pk v'}{pre : SystemState} {post : SystemState} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → (ivnp : IsValidNewPart (_vSignature v') pk theStep)
                     → firstSendEstablishes v' pk pre theStep
  isValidNewPart⇒fSE {pre = pre} {theStep = step-peer {pid = β} {outs = outs} pstep} hpk (_ , ¬init , ¬sentb4 , mws , _)
     with Any-++⁻ (actionsToSentMessages β outs) (msg∈pool mws)
     -- TODO-1 : Much of this proof is not specific to the particular property being proved, and could be
     -- refactored into Yasm.Properties.  See proof of unwind and refactor to avoid redundancy?
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
     with pstep
  ...| step-cheat isCheat
     with thisStep
  ...| here refl
     with isCheat (msg⊆ mws) (msgSigned mws) (transp-¬∈BootstrapInfo₁ ¬init mws)
  ...| inj₁ dis = ⊥-elim (hpk dis)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)

  isValidNewPart⇒fSE {pk}{v'}{pre}{theStep = step-peer {β} {postst} {outs} {.pre} pstep} hpk (r , ¬init , ¬sentb4 , mws , refl , zefl , vpk)
     | inj₁ thisStep
     | step-honest {.β} hstep
     with senderMsgPair∈⇒send∈ outs thisStep
  ...| nm∈outs , refl
     with hstep
  ...| step-msg {_ , P m} m∈pool ini
     with ⊎-elimʳ (¬subst ¬sentb4 (msgSameSig mws))
                  (impl-sps-avp {m = msgWhole mws} r hpk hstep nm∈outs (msg⊆ mws) (msgSigned mws) (transp-¬∈BootstrapInfo₁ ¬init mws))
  ...| (vpk' , _)
     with noEpochIdChangeYet {ppre = peerStates pre β} r refl hstep ini
  ...| eids≡
     with newVoteSameEpochGreaterRound r hstep (¬subst ¬init (msgSameSig mws)) hpk (msg⊆ mws) nm∈outs (msgSigned mws)
                                               (¬subst ¬sentb4 (msgSameSig mws))
  ...| refl , newlvr
     with StepPeer-post-lemma pstep
  ...| post≡ = r , ¬sentb4 , mkCarrier (step-s r (step-peer (step-honest hstep)))
                                       mws
                                       (override-target-≡ {a = β})
                                       vpk'
                                       (inj₂ ( trans eids≡ (auxEid post≡)
                                             , ≤-reflexive (trans newlvr (auxLvr post≡))))
                                       where auxEid = cong (_^∙ rmEpoch)
                                             auxLvr = cong (_^∙ rmLastVotedRound)

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
     with (msgPart (carrSent prop)) ^∙ vEpoch ≟ (peerStates pre (msgSender (carrSent prop))) ^∙ rmEpoch
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

  vo₁ : Common.IncreasingRoundObligation 𝓔
  -- Initialization doesn't send any messages at all so far; Agda figures that out so no proof
  -- required here.  In future it may send messages, but any verifiable Signatures for honest PKs
  -- they contain will be from BootstrapInfo.
  vo₁ {pid} {pk = pk} {pre = pre} r sm@(step-msg {(_ , nm)} m∈pool pidini)
      {m = m} {v'} hpk v⊂m m∈outs sig ¬init ¬sentb4 vspk v'⊂m' m'∈pool sig' ¬init' refl
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the poststate of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of the peer that
     -- sent v'
     with Any-Step-elim {Q = LvrCarrier pk (_vSignature v') pre}
                        (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-map (λ _ ivnp → isValidNewPart⇒fSE {v' = v'} hpk ivnp)
                                      (unwind r hpk v'⊂m' m'∈pool sig' ¬init'))
  ...| mkCarrier r' mws ini vpf' preprop
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with sameSig⇒sameVoteData (msgSigned mws) sig' (msgSameSig mws)
  ...| inj₁ hb = ⊥-elim (PerReachableState.meta-sha256-cr r hb)
  ...| inj₂ refl
     with msgSender mws ≟NodeId pid
  ...| no neq =
     -- We know that *after* the step, pid can sign v (vpb is about the post-state).  For v', we
     -- know it about state "pre"; we transport this to the post-state using
     -- PeerCanSignForPK-Stable.  Because EpochConfigs known in a system state are consistent with
     -- each other (i.e., trivially, for now because only the initial EpochConfig is known), we can
     -- use PK-inj to contradict the assumption that v and v' were sent by different peers (neq).
     let vpb     = proj₁ (⊎-elimʳ ¬sentb4 (impl-sps-avp r hpk sm m∈outs v⊂m sig ¬init))
         theStep = step-peer (step-honest sm)
         vpf''   = PeerCanSignForPK-stable r theStep vpf'
         𝓔s≡     = availEpochsConsistent {pid} {msgSender mws} vpb vpf'' refl
     in  ⊥-elim (neq (trans (trans (sym (nid≡ (pcs4in𝓔 vpf'')))
                                   (PK-inj-same-ECs (sym 𝓔s≡)
                                                    (trans (pk≡ (pcs4in𝓔 vpf'')) (sym (pk≡ (pcs4in𝓔 vpb))))))
                            (nid≡ (pcs4in𝓔 vpb))))

  ...| yes refl -- Same peer sends both v and v'
     with newVoteSameEpochGreaterRound r (step-msg m∈pool ini) ¬init hpk v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , refl
     with msgsToSendWereSent {pid} {nm} m∈outs
  ...| _ , _ , _ , refl
     with preprop
  ...| inj₁ diffEpoch = ⊥-elim (diffEpoch eIds≡')
  ...| inj₂ (sameEpoch , v'rnd≤lvr) = inj₁ (s≤s v'rnd≤lvr)

  -- TODO-1: This proof should be refactored to reduce redundant reasoning about the two votes.  The
  -- newVoteSameEpochGreaterRound property uses similar reasoning.

  vo₂ : VO.ImplObligation₂ 𝓔
  vo₂ {pid = pid} {pk = pk} {pre = pre} r (step-msg {_ , nm} m∈pool pinit) {v = v} {m}
      hpk v⊂m m∈outs sig ¬init vnew vpk v'⊂m' m'∈outs sig' ¬init' v'new vpk' es≡ rnds≡
     with msgsToSendWereSent {pid} {nm} m∈outs
  ...| _ , vm , pm , refl
    with m∈outs
  ...| here refl
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inSI si∈m qc∈si)
                  rewrite cong _vSignature v≈rbld
     with qcVotesSentB4 r pinit
                        (VoteMsgQCsFromRoundManager r (step-msg m∈pool pinit) hpk v⊂m m∈outs (obm-dangerous-magic' "see Handle.Properties")) vs∈qc ¬init
  ...| mws = ⊥-elim (vnew mws)

  vo₂ {pid = pid} {pk = pk} {pre = pre} r (step-msg {_ , nm} m∈pool pinit) {v = v} {m} {v'} {m'}
      hpk v⊂m m∈outs sig ¬init vnew vpk v'⊂m' m'∈outs sig' ¬init' v'new vpk' es≡ rnds≡
     | _ , vm , pm , refl
     | here refl
     | vote∈vm
     with msgsToSendWereSent {pid} {nm} {m'} {st = peerStates pre pid} m'∈outs
  ...| _ , vm' , pm' , refl
     with m'∈outs
  ...| here refl
     with v'⊂m'
  ...| vote∈vm = refl
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inSI si∈m qc∈si)
                  rewrite cong _vSignature v≈rbld
     with qcVotesSentB4 r pinit
                       (VoteMsgQCsFromRoundManager r (step-msg m∈pool pinit) hpk v'⊂m' m'∈outs (obm-dangerous-magic' "see Handle.Properties")) vs∈qc ¬init'
  ...| mws = ⊥-elim (v'new mws)
