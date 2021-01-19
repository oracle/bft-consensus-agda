{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr
open import LibraBFT.Impl.Properties.Aux

open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.VotesOnce as VO

open import LibraBFT.Yasm.AvailableEpochs as AE
open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms
open        Structural impl-sps-avp

open import LibraBFT.Concrete.Obligations

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  postulate  -- TODO : prove
    newVoteSameEpochGreaterRound : ∀ {e 𝓔s pid pool ms s s' outs v m pk}
                                 → StepPeerState {e} pid 𝓔s pool ms s' outs
                                 → ms ≡ just s
                                 → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                                 → ¬ MsgWithSig∈ pk (ver-signature sig) pool
                                 → (v ^∙ vEpoch) ≡ (₋epEC s) ^∙ epEpoch
                                 × suc ((₋epEC s) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                                 × (v ^∙ vRound) ≡ ((₋epEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote

    noEpochChangeYet : ∀ {e pid 𝓔s pool outs ps ps'}
                     → StepPeerState {e} pid 𝓔s pool (just ps) ps' outs
                     → (₋epEC ps') ^∙ epEpoch ≡ (₋epEC ps) ^∙ epEpoch  -- Always true, so far, as no epoch changes.


    lastVoteRound-mono : ∀ {e e'}{pre : SystemState e}{post : SystemState e'}{pid}
                       → Step pre post
                       → (ij : Is-just (Map-lookup pid (peerStates pre)))
                       → Σ (Is-just (Map-lookup pid (peerStates post)))
                           λ ij' → ((₋epEC (to-witness ij') ^∙ epEpoch ≡ (₋epEC (to-witness ij)) ^∙ epEpoch  -- Always true, so far, as no epoch changes.
                                    → (₋epEC (to-witness ij)) ^∙ epLastVotedRound ≤ (₋epEC (to-witness ij')) ^∙ epLastVotedRound))
{-
    noMsgsByUninitialised : ∀ {e} {st : SystemState e} {pid} {m}
                          → ReachableSystemState st
                          → (pid , m) ∈ msgPool st
                          → Is-just (Map-lookup pid (peerStates st))
-}


  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.  TODO-1: this needs a better name!

  record WhatWeWant (pk : PK) (sig : Signature) {e} (st : SystemState e) : Set where
    constructor mkWhatWeWant
    field
      wwwOrigE      : ℕ
      wwwOrigSt     : SystemState wwwOrigE
      wwwSent       : MsgWithSig∈ pk sig (msgPool wwwOrigSt)
      wwwValid      : ValidPartForPK (availEpochs st) (msgPart wwwSent) pk
      wwwOrigSndr   : NodeId
      wwwOrigSndr≡  : wwwOrigSndr ≡ EpochConfig.toNodeId (vp-ec wwwValid) (vp-member wwwValid) 
      wwwIsJust     : Is-just (Map-lookup wwwOrigSndr (peerStates st))
      wwwLvr        : (msgPart wwwSent) ^∙ vRound ≤ (₋epEC (to-witness wwwIsJust)) ^∙ epLastVotedRound
  open WhatWeWant

  firstSendEstablishes : ∀ {e} → Vote → PK → SystemState e → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-epoch _) = ⊥ 
  firstSendEstablishes _ _ _ (step-peer (step-cheat _ _)) = ⊥
  firstSendEstablishes {e} v' pk origSt sysStep@(step-peer {e'} {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × Σ (WhatWeWant pk (signature v' unit) origSt) λ www →
                             Σ (e ≡ wwwOrigE www) λ refl →
                               wwwOrigSt www ≡ subst SystemState refl origSt
                         )

  isValidNewPart⇒fSE : ∀ {e e' pk v'}{pre : SystemState e} {post : SystemState e'} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → IsValidNewPart (₋vSignature v') pk theStep
                     → firstSendEstablishes v' pk post theStep
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
     | step-honest x
     with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs
     with impl-sps-avp {m = msgWhole mws} pre r hpk x nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ ((vpk' , refl) , _)
     with x
  ...| step-init _ refl = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {s' = st} m∈pool ms≡ handle≡
     with sameEpoch⇒sameEC vpk vpk' refl
  ...| refl
     with toℕ-injective (sameEC⇒sameMember vpk vpk' refl)
  ...| refl
     with newVoteSameEpochGreaterRound x ms≡ (msg⊆ mws) nm∈outs (msgSigned mws) (subst (λ sig → ¬ MsgWithSig∈ pk sig (msgPool pre)) (sym (msgSameSig mws)) ¬sentb4)
  ...| _ , refl , newlvr = r , ¬sentb4
                         , (mkWhatWeWant e' post mws vpk β refl (isJust Map-set-correct)
                                         (≤-reflexive (trans newlvr
                                                             (cong ((_^∙ epLastVotedRound) ∘ ₋epEC)
                                                                   (sym (to-witness-isJust-≡ {prf = (Map-set-correct {mv = just st})}))))))
                         , refl , refl
  
  WhatWeWant-transp : ∀ {e e' e'' pk sig} {orig : SystemState e} {pre : SystemState e'}{post : SystemState e''}
                     → (theStep : Step pre post)
                     → WhatWeWant pk sig pre
                     → WhatWeWant pk sig post
  WhatWeWant-transp {e} {pre = pre} {post} (step-epoch ec) (mkWhatWeWant origE origSt mws vpk origSndr refl ij lvr) =
    mkWhatWeWant origE origSt mws (ValidPartForPK-stable-epoch ec vpk) origSndr (epochPreservestoNodeId vpk) ij lvr
  WhatWeWant-transp {e' = e'} {pre = pre} {post} sp@(step-peer {pid = pid} {st'} {pre = .pre} sps) (mkWhatWeWant origE origSt mws vpk origSndr refl ij lvr)
     with origSndr ≟ℕ pid
  ...| no diff rewrite Map-set-target-≢ {k = pid} {k' = origSndr} {mv = st'} {m = peerStates pre} diff =
               mkWhatWeWant origE origSt mws vpk origSndr refl ij lvr
  ...| yes refl
     with sps
  ...| step-cheat fm isch rewrite cheatStepDNMPeerStates (step-cheat {pre = pre} fm isch) unit =
                  mkWhatWeWant origE origSt mws vpk origSndr refl ij (≤-trans lvr (≤-reflexive refl)) -- PeerStates not changed by cheat steps
  ...| step-honest (step-init _ handle≡) = {!!}
                                         -- We cannot prove this yet because
                                         -- initialEventProcessorAndMessages is faked for now.  We
                                         -- need to establish rules for what initialization by a
                                         -- peer pid does.  It must ensure that if pid's new
                                         -- peerState is for epoch e and has lastVotedRound = r,
                                         -- then pid has not previously sent any messages containing
                                         -- votes for the epoch e and for a round higher than r.

  ...| theStep@(step-honest msgStep@(step-msg {s = s} {s' = s'}{outs = outs} m∈pool ps≡pre handler≡))
     -- If the epoch doesn't change (which it never does, so far), then the lastVotedRound is
     -- monotonically nondecreasing for each honest peer step.
     with lastVoteRound-mono (step-peer theStep) ij
  ...| ij' , lvrmono
     -- Now we need some annoying translation between Is-just and known values, so we can invoke
     -- noEpochChangeYet for this step.  Makes me wonder why we use Is-just, why not just use an
     -- existential?  Or maybe recast noEpochChangeYet?
     with (trans ps≡pre (cong just (to-witness-known-value ij ps≡pre)))
  ...| justs≡witij
       with to-witness-known-value ij' Map-set-correct
  ...| s'≡witij'
     with subst₂ (λ mspre pspost → StepPeerState origSndr (availEpochs pre) (msgPool pre) mspre pspost outs)
                 justs≡witij s'≡witij' msgStep
  ...| msgStep' = mkWhatWeWant origE origSt mws vpk origSndr refl ij'
                                (≤-trans lvr (lvrmono (noEpochChangeYet msgStep')))

  WhatWeWant-transp* : ∀ {e e' pk sig} {start : SystemState e}{final : SystemState e'}
                     → WhatWeWant pk sig start
                     → (step* : Step* start final)
                     → WhatWeWant pk sig final
  WhatWeWant-transp* www step-0 = www
  WhatWeWant-transp* {start = start} www (step-s s* s) = WhatWeWant-transp {orig = start} s (WhatWeWant-transp* www s*)
  
  fSE⇒rnd≤lvr : ∀ {v' pk e'}
              → {final : SystemState e'}
              → Meta-Honest-PK pk
              → ∀ {d d'}{pre : SystemState d} {post : SystemState d'}{theStep : Step pre post}
              → firstSendEstablishes v' pk post theStep
              → (step* : Step* post final)
              → WhatWeWant pk (signature v' unit) final
  fSE⇒rnd≤lvr _ {theStep = step-epoch _} ()
  fSE⇒rnd≤lvr {v' = v'} {pk} hpk {e} {pre = pre} {post} {theStep = step-peer {pid = β} {outs = outs} (step-honest sps)} (r , ¬sentb4 , www@(mkWhatWeWant origE origSt mws _ _ _ _ _) , refl , refl) step*
     with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} (msg∈pool mws)
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
       with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs rewrite sym (msgSameSig mws)
     with impl-sps-avp {m = nm} pre r hpk sps nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ ((vpk'' , sender) , _) rewrite msgSameSig mws = WhatWeWant-transp* www step*

  vo₁ : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁ r (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₁ {e} {pk = pk} {pre = pre} r sm@(step-msg {s = ps} {s' = ps'} _ ps≡ _) {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 (vpb , refl) v'⊂m' m'∈pool sig' eIds≡ rnds≡
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the post state of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of pid (the peer that
     -- sent v')
     with Any-Step-elim (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE hpk ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| mkWhatWeWant origE origSt mws vpf' origSndr refl ij v'rnd≤lvr
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with newVoteSameEpochGreaterRound {e} {availEpochs pre} sm ps≡ v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     with sameHonestSig⇒sameVoteData hpk (msgSigned mws) sig' (msgSameSig mws)
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre r hb)
  ...| inj₂ refl
     -- Both votes have the same epochID, therefore same EpochConfig
     with sameEpoch⇒sameEC vpb vpf' eIds≡
  ...| refl
     -- Because the votes have the same EpochConfig and same PK, they are by
     -- the same member
     with toℕ-injective (sameEC⇒sameMember vpb vpf' refl)
  ...| refl
     -- Therefore they are by the same peer
     -- So the peerState the sender of v' is the same as the peerState of the peer taking this step
     with just-injective (trans (sym ps≡) (to-witness-lemma ij refl))
     -- Now we can establish a contradiction with the hypothesis that the rounds of v and v' are equal
  -- TODO-1: this may be overly complicated now that rnd≡ is an equality
  ...| refl rewrite rnds≡ = ⊥-elim (<⇒≢ (≤-reflexive suclvr≡v'rnd) (≤-antisym (<⇒≤ (≤-reflexive suclvr≡v'rnd)) v'rnd≤lvr))

  postulate  -- TODO : prove
    vo₂ : VO.ImplObligation₂
