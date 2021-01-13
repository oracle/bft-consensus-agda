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

{- Unused, so far
    noEpochChangeYet : ∀ {e pid 𝓔s pool outs ps' ps}
                     → StepPeerState {e} pid 𝓔s pool (just ps') ps outs
                     → (₋epEC ps) ^∙ epEpoch ≡ (₋epEC ps') ^∙ epEpoch

    lastVoteRound-mono : ∀ {e pid 𝓔s pool outs ps' ps}
                       → StepPeerState {e} pid 𝓔s pool (just ps') ps outs
                       → (₋epEC ps') ^∙ epEpoch ≡ (₋epEC ps) ^∙ epEpoch  -- Always true, so far, as no epoch changes.
                       → (₋epEC ps') ^∙ epLastVotedRound ≤ (₋epEC ps) ^∙ epLastVotedRound

    noMsgsByUninitialised : ∀ {e} {st : SystemState e} {pid} {m}
                          → ReachableSystemState st
                          → (pid , m) ∈ msgPool st
                          → Is-just (Map-lookup pid (peerStates st))
-}

  WhatWeWant : ∀ {e} → PK → Signature → SystemState e → Set
  WhatWeWant pk sig st = Σ (MsgWithSig∈ pk sig (msgPool st))
                           λ mws → Σ (ValidPartForPK (availEpochs st) (msgPart mws) pk)
                                     λ vpf → Σ (Is-just (Map-lookup (EpochConfig.toNodeId (vp-ec vpf) (vp-member vpf)) (peerStates st)))
                                               λ ij → (msgPart mws) ^∙ vRound ≤ (₋epEC (to-witness ij)) ^∙ epLastVotedRound

  firstSendEstablishes : Vote → PK → SystemStateRel Step
  firstSendEstablishes _ _ (step-epoch _) = ⊥ 
  firstSendEstablishes _ _ (step-peer (step-cheat _ _)) = ⊥
  firstSendEstablishes v' pk {e} {.e} sysStep@(step-peer {pid = pid'} {pre = pre} pstep@(step-honest {st = pst} {outs} _)) =
                       Σ (IsValidNewPart (signature v' unit) pk sysStep) λ ivnp → WhatWeWant pk (signature v' unit) (StepPeer-post pstep)

  isValidNewPart⇒fSE : ∀ {e e' pk v'}{pre : SystemState e} {post : SystemState e'} {theStep : Step pre post}
                     → Meta-Honest-PK pk
                     → IsValidNewPart (₋vSignature v') pk theStep
                     → firstSendEstablishes v' pk theStep
  isValidNewPart⇒fSE {pre = pre}{theStep = step-peer {pid = β} {outs = outs} pstep} hpk (¬sentb4 , mws , _)
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

  isValidNewPart⇒fSE {pk = pk}{v'}{pre}{post}{theStep = step-peer {pid = β} {outs = outs} pstep} hpk (¬sentb4 , mws , vpk)
     | inj₁ thisStep
     | step-honest x
     with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs
     with impl-sps-avp {m = msgWhole mws} pre hpk x nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ ((vpk' , sender) , _)
     with x
  ...| step-init _ refl = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {s' = st} m∈pool ms≡ handle≡
     with sameEpoch⇒sameEC vpk vpk' refl
  ...| refl
     with toℕ-injective (sameEC⇒sameMember vpk vpk' refl)
  ...| refl
     with newVoteSameEpochGreaterRound x ms≡ (msg⊆ mws) nm∈outs (msgSigned mws) (subst (λ sig → ¬ MsgWithSig∈ pk sig (msgPool pre)) (sym (msgSameSig mws)) ¬sentb4)
  ...| _ , refl , newlvr
     with Map-set-correct {k = β} {mv = just st} {m = peerStates pre}
  ...| maps≡
     with subst (λ β' → Map-lookup β' (Map-set β (just st) (peerStates pre)) ≡ just st) (sym sender) Map-set-correct
  ...| psUpdated
       = (¬sentb4 , (mws , vpk))
                         , (mws
                           , vpk
                           , (isJust psUpdated)
                           , ≤-reflexive (trans newlvr
                                                (cong ((_^∙ epLastVotedRound) ∘ ₋epEC)
                                                      (sym (to-witness-isJust-≡ {prf = psUpdated})))))

  postulate
    transp-WhatWeWant : ∀ {e e' pk v'} {start : SystemState e}{final : SystemState e'}
                    → WhatWeWant pk v' start
                    → Step* start final
                    → WhatWeWant pk v' final

    -- We will use impl-sps-avp to establish the first conjunct of firstsendestablishes; it no
    -- longer needs to know its pre-state is reachable, which is inconvenient to know here.

  fSE⇒rnd≤lvr : ∀ {e e' e'' v' pk}{pre : SystemState e} {post : SystemState e'}{final : SystemState e''} {theStep : Step pre post}
              → Meta-Honest-PK pk
              → firstSendEstablishes v' pk theStep
              → Step* post final
              → WhatWeWant pk (signature v' unit) final
  fSE⇒rnd≤lvr {theStep = step-epoch _} _ ()
  fSE⇒rnd≤lvr {theStep = step-peer (step-cheat _ _)} _ ()
  fSE⇒rnd≤lvr {e} {v' = v'} {pk} {pre} {theStep = step-peer {pid = β} {outs = outs} (step-honest sps)} hpk ((¬sentb4 , mws , vpk) , (mws' , vpk' , ij , xxx)) step*
     with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} (msg∈pool mws)
  ...| inj₂ furtherBack = ⊥-elim (¬sentb4 (MsgWithSig∈-transp mws furtherBack))
  ...| inj₁ thisStep
       with Any-satisfied-∈ (Any-map⁻ thisStep)
  ...| nm , refl , nm∈outs rewrite sym (msgSameSig mws)
     with impl-sps-avp {m = nm} pre hpk sps nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ ((vpk'' , sender) , xx) = transp-WhatWeWant (mws' , vpk' , (ij , xxx)) step*

  vo₁-unwind2 : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁-unwind2 r (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₁-unwind2 {e} {pk = pk} {pre = pre} r sm@(step-msg {s = ps} {s' = ps'} _ ps≡ _) {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 (vpb , pid≡) v'⊂m' m'∈pool sig' eIds≡ rnds≡
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the post state of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of pid (the peer that
     -- sent v')
     with Any-Step-elim (fSE⇒rnd≤lvr {v' = v'} hpk)
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE hpk ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| mws , vpf' , ij , v'rnd≤lvr
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
     with trans (sym pid≡) ((cong (EpochConfig.toNodeId (vp-ec vpb)) refl))
  ...| refl
     -- So the peerState the sender of v' is the same as the peerState of the peer taking this step
     with just-injective (trans (sym ps≡) (to-witness-lemma ij refl))
     -- Now we can establish a contradiction with the hypothesis that the rounds of v and v' are equal
  -- TODO-1: this may be overly complicated now that rnd≡ is an equality
  ...| refl rewrite rnds≡ = ⊥-elim (<⇒≢ (≤-reflexive suclvr≡v'rnd) (≤-antisym (<⇒≤ (≤-reflexive suclvr≡v'rnd)) v'rnd≤lvr))

--   postulate  -- TODO : prove
--     vo₂ : VO.ImplObligation₂
