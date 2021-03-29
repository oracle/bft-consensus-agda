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

open import LibraBFT.Impl.Consensus.Types hiding (EpochConfigFor)
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor.Properties  sha256 sha256-cr
open import LibraBFT.Impl.Handle                                          sha256 sha256-cr
open import LibraBFT.Impl.Handle.Properties                               sha256 sha256-cr
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Properties.Aux
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm (ℓ+1 0ℓ) EpochConfig epochId authorsN ConcSysParms NodeId-PK-OK
open        Structural impl-sps-avp

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  postulate  -- TODO-2: prove.  Note that these are really just properties about the handler,
             -- but are currently wrapped up into properties about SystemState.  These should
             -- probably be "unbundled" and move to LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor
    newVoteSameEpochGreaterRound : ∀ {e 𝓔s pid pool ms s s' outs v m pk}
                                 → StepPeerState {e} pid 𝓔s pool ms (s' , outs)
                                 → just s ≡ ms
                                 → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                                 → ¬ MsgWithSig∈ pk (ver-signature sig) pool
                                 → (v ^∙ vEpoch) ≡ (₋epEC s) ^∙ epEpoch
                                 × suc ((₋epEC s) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                                 × (v ^∙ vRound) ≡ ((₋epEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote

    -- Always true, so far, as no epoch changes.
    noEpochChangeYet : ∀ {e}{pre : SystemState e}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → StepPeerState pid (availEpochs pre) (msgPool pre) (just ppre) (ppost , msgs)
                     → just ppre ≡ Map-lookup pid (peerStates pre)
                     → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch

    -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
    lastVoteRound-mono : ∀ {e}{pre : SystemState e}{pid}{ppre ppost msgs}
                       → ReachableSystemState pre
                       → just ppre ≡ Map-lookup pid (peerStates pre)
                       → StepPeerState pid (availEpochs pre) (msgPool pre) (just ppre) (ppost , msgs)
                       → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch
                       → (₋epEC ppre) ^∙ epLastVotedRound ≤ (₋epEC ppost) ^∙ epLastVotedRound

  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.
  -- TODO-2: Only lvrcLvr is specific to the property we are proving here, so much of this
  -- can be refactored into Yasm.Properties, paramerized by a predicate over Part and PeerState,
  -- along with a proof that every honest peer step preserves it.  This will provide useful
  -- infrastructure for proving other properties.

  LvrProp : CarrierProp
  LvrProp v mep = ∃[ ep ]( mep ≡ just ep
                         × (  v ^∙ vEpoch ≢ (₋epEC ep) ^∙ epEpoch
                           ⊎ (v ^∙ vEpoch ≡ (₋epEC ep) ^∙ epEpoch × v ^∙ vRound ≤ (₋epEC ep) ^∙ epLastVotedRound)))

  LvrCarrier = PropCarrier LvrProp
 
  firstSendEstablishes : ∀ {e} → Vote → PK → (origSt : SystemState e) → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-epoch _)               = Lift (ℓ+1 0ℓ) ⊥
  firstSendEstablishes _ _ _ (step-peer (step-cheat _ _)) = Lift (ℓ+1 0ℓ) ⊥
  firstSendEstablishes {e} v' pk origSt sysStep@(step-peer {e'} {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × LvrCarrier pk (₋vSignature v') (StepPeer-post pstep)
                         )
  isValidNewPart⇒fSE : ∀ {e e' pk v'}{pre : SystemState e} {post : SystemState e'} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → (ivnp : IsValidNewPart (₋vSignature v') pk theStep)
                     → firstSendEstablishes v' pk pre theStep
  isValidNewPart⇒fSE {pre = pre}{theStep = step-peer {pid = β} {outs = outs} pstep} hpk (_ , ¬sentb4 , mws , _)
     with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} (msg∈pool mws)
     -- TODO-1 : DRY fail, see proof of unwind, refactor?
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
     with pstep
  ...| step-cheat fm isCheat
     with thisStep
  ...| here refl
     with isCheat (msg⊆ mws) (msgSigned mws)
  ...| inj₁ dis = ⊥-elim (hpk dis)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)

  isValidNewPart⇒fSE {e' = e'}{pk}{v'}{pre}{post}{theStep = step-peer {pid = β} {outs = outs} pstep} hpk (r , ¬sentb4 , mws , vpk)
     | inj₁ thisStep
     | step-honest hstep
     with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs
     with impl-sps-avp {m = msgWhole mws} r hpk hstep nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ (vpk' , _)
     with hstep
  ...| step-init _ = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {m} {s = s} m∈pool ms≡
     with sameEpoch⇒sameEC vpk vpk' refl
  ...| refl
     with newVoteSameEpochGreaterRound hstep ms≡ (msg⊆ mws) nm∈outs (msgSigned mws)
                                       (subst (λ sig → ¬ MsgWithSig∈ pk sig (msgPool pre))
                                              (sym (msgSameSig mws))
                                              ¬sentb4)
  ...| refl , refl , newlvr
     with LBFT-post (handle m 0) s | inspect (LBFT-post (handle m 0)) s
  ...| ps' | [ refl ] rewrite sym ms≡ = r , ¬sentb4 , mkCarrier (step-s r (step-peer pstep)) mws vpk
                                                (just ps')
                                                Map-set-correct
                                                (ps' , refl , inj₂ (noEpochChangeYet r hstep ms≡ , ≤-reflexive newlvr))

  ImplPreservesLvr : PeerStepPreserves LvrProp
  ImplPreservesLvr r _ (step-init ix) = magic
    where postulate  -- TODO-2: temporary until real initialisation is modeled
            -- We don't have a real model for the initial peer state, so here we just postulate.
            -- Eventually, we'll prove something like a peer doesn't initialize to an epoch for which
            -- it has already sent votes.
            magic : LvrProp v (just fakeEP)
  ImplPreservesLvr {pre = pre} r prop (step-msg {m} {s} m∈pool ms≡justs)
     with carrProp prop
  ...| (ppre' , ppre≡ , preprop)
     with just-injective (trans ms≡justs (trans (carrSndrSt≡ prop) ppre≡))
  ...| refl
     with noEpochChangeYet r (step-msg m∈pool refl) ms≡justs
  ...| stepDNMepoch
     with preprop
  ...| inj₁ diffEpoch = LBFT-post (handle m 0) ppre' , refl , inj₁ λ x → diffEpoch (trans x (sym stepDNMepoch))
  ...| inj₂ (sameEpoch , rnd≤ppre)
     with (msgPart (carrSent prop)) ^∙ vEpoch ≟ (₋epEC ppre') ^∙ epEpoch
  ...| no neq = LBFT-post (handle m 0) ppre'
              , refl
              , ⊥-elim (neq sameEpoch)
  ...| yes refl
     with lastVoteRound-mono {ppre = ppre'} r ms≡justs (step-msg m∈pool refl)
  ...| es≡⇒lvr≤
     = LBFT-post (handle m 0) ppre'
     , refl
     , inj₂ (stepDNMepoch , ≤-trans rnd≤ppre (es≡⇒lvr≤ stepDNMepoch))

  LvrCarrier-transp : ∀ {e' e'' pk sig} {pre : SystemState e'}{post : SystemState e''}
                     → (theStep : Step pre post)
                     → LvrCarrier pk sig pre
                     → LvrCarrier pk sig post
  LvrCarrier-transp {e'} {e''} {pk} {sig} {pre = pre} {post} = (Carrier-transp LvrProp) ImplPreservesLvr

  LvrCarrier-transp* : ∀ {e e' pk sig} {start : SystemState e}{final : SystemState e'}
                     → LvrCarrier pk sig start
                     → (step* : Step* start final)
                     → LvrCarrier pk sig final
  LvrCarrier-transp* lvrc step-0 = lvrc
  LvrCarrier-transp* {start = start} lvrc (step-s s* s) = LvrCarrier-transp s (LvrCarrier-transp* lvrc s*)

  fSE⇒rnd≤lvr : ∀ {v' pk e'}
              → {final : SystemState e'}
              → Meta-Honest-PK pk
              → ∀ {d d'}{pre : SystemState d}{post : SystemState d'}{theStep : Step pre post}
              → firstSendEstablishes v' pk post theStep
              → (step* : Step* post final)
              → LvrCarrier pk (signature v' unit) final
  fSE⇒rnd≤lvr _ {theStep = step-epoch _} ()
  fSE⇒rnd≤lvr {v' = v'} {pk} hpk {pre = pre} {post} {theStep = step-peer {pid = β} {outs = outs} (step-honest sps)}
              (r , ¬sentb4 , lvrc@(mkCarrier r' mws vpk spre spre≡ lvr)) step*
              = LvrCarrier-transp* lvrc step*

  vo₁ : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁ r (step-init _) _ _ m∈outs _ _ _ _ _ _ _ _ = ⊥-elim (¬Any[] m∈outs)
  vo₁ {e} {pid} {pk = pk} {pre = pre} r (step-msg m∈pool ps≡)
      {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 vpb v'⊂m' m'∈pool sig' refl rnds≡
     with newVoteSameEpochGreaterRound {e} {availEpochs pre} {pid}
                                       (step-msg m∈pool ps≡) ps≡ v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the poststate of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of the peer that
     -- sent v'
     with Any-Step-elim {Q = LvrCarrier pk (₋vSignature v') pre}
                        (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE {v' = v'} hpk ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| mkCarrier r' mws vpf' sndrst sndrst≡ (_ , ps≡' , preprop)
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with sameHonestSig⇒sameVoteData hpk (msgSigned mws) sig' (msgSameSig mws)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre r hb)
  ...| inj₂ refl
     -- Both votes have the same epochID, therefore same EpochConfig
     with sameEpoch⇒sameEC vpb vpf' refl
                    -- Both peers are allowed to sign for the same PK, so they are the same peer
  ...| refl rewrite NodeId-PK-OK-injective (vp-ec vpb) (vp-sender-ok vpb) (vp-sender-ok vpf') |
                    -- So their peer states are the same
                    sym (just-injective (trans (trans ps≡ sndrst≡) ps≡'))
     with noEpochChangeYet r' (step-msg m∈pool refl) ps≡
  ...| stepDNMepoch
     with preprop
  ...| inj₁ diffEpoch = ⊥-elim (diffEpoch eIds≡')
  ...| inj₂ (sameEpoch , v'rnd≤lvr)
                    -- So we have proved both that the round of v' is ≤ the lastVotedRound of
                    -- the peer's state and that the round of v' is one greater than that value,
                    -- which leads to a contradiction
                    = ⊥-elim (1+n≰n (≤-trans (≤-reflexive suclvr≡v'rnd)
                                             (≤-trans (≤-reflexive rnds≡) v'rnd≤lvr)))

  vo₂ : VO.ImplObligation₂
  vo₂ _ (step-init _) _ _ m∈outs _ _ _ _ _ _ _ _ = ⊥-elim (¬Any[] m∈outs)
  vo₂ {pk = pk} {st} r (step-msg {pid , nm} {s = ps} _ ps≡) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig vnew vpk v'⊂m' m'∈outs sig' v'new vpk' es≡ rnds≡
    with nm
  ...| P msg
    with msgsToSendWereSent {pid} {0} {P msg} {m} {ps} m∈outs
  ...| vm , refl , vmSent
    with msgsToSendWereSent1 {pid} {0} {msg} {vm} {ps} vmSent
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
                        | procPMCerts≡ {0} {msg} {ps} {vm} v∈outs
     = ⊥-elim (vnew (qcVotesSentB4 r ps≡ qc∈m refl vs∈qc))
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
                        | procPMCerts≡ {0} {msg} {ps} {vm} v∈outs
     = ⊥-elim (v'new (qcVotesSentB4 r ps≡ qc∈m refl vs∈qc))
