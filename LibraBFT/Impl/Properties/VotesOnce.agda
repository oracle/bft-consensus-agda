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
                                 → StepPeerState {e} pid 𝓔s pool ms s' outs
                                 → ms ≡ just s
                                 → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                                 → ¬ MsgWithSig∈ pk (ver-signature sig) pool
                                 → (v ^∙ vEpoch) ≡ (₋epEC s) ^∙ epEpoch
                                 × suc ((₋epEC s) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                                 × (v ^∙ vRound) ≡ ((₋epEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote

    -- Always true, so far, as no epoch changes.
    noEpochChangeYet : ∀ {e e'}{pre : SystemState e}{post : SystemState e'}{pid}{ppre ppost}
                        → Step pre post -- Might or might not be a step by pid
                        → Map-lookup pid (peerStates pre)  ≡ just ppre
                        → Map-lookup pid (peerStates post) ≡ just ppost
                        → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch

    epoch≡stepPeer : ∀ {e}{st : SystemState e}{pid s}
                   → ReachableSystemState st
                   → Map-lookup pid (peerStates st) ≡ just s
                   → (₋epEC s) ^∙ epEpoch ≡ epochId (α-EC (₋epEC s , ₋epEC-correct s))

    newVoteGreaterRound : ∀ {e 𝓔s pid pool ms s s' outs v m pk}
                        → StepPeerState {e} pid 𝓔s pool ms s' outs
                        → ms ≡ just s
                        → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                        → (v ^∙ vRound) ≡ suc ((₋epEC s) ^∙ epLastVotedRound)


    -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
    lastVoteRound-mono' : ∀ {e e'}{pre : SystemState e}{post : SystemState e'}{pid}{ppre ppost}
                        → Step pre post -- Might or might not be a step by pid
                        → Map-lookup pid (peerStates pre)  ≡ just ppre
                        → Map-lookup pid (peerStates post) ≡ just ppost
                        → (₋epEC ppre) ^∙ epEpoch ≡ (₋epEC ppost) ^∙ epEpoch
                        → (₋epEC ppre) ^∙ epLastVotedRound ≤ (₋epEC ppost) ^∙ epLastVotedRound
{-
  -- This is the information we can establish about the state after the first time a signature is
  -- sent, and that we can carry forward to subsequent states, so we can use it to prove
  -- VO.ImplObligation₁.
  -- TODO-2: Only lvrcLvr is specific to the property we are proving here, so much of this
  -- can be refactored into Yasm.Properties, paramerized by a predicate over Part and PeerState,
  -- along with a proof that every honest peer step preserves it.  This will provide useful
  -- infrastructure for proving other properties.
  record LvrCarrier (pk : PK) (sig : Signature) {e} (st : SystemState e) : Set₁ where
    constructor mkLvrCarrier
    field
      lvrcSent    : MsgWithSig∈ pk sig (msgPool st)
      lvrcValid   : ValidSenderForPK (availEpochs st) (msgPart lvrcSent) (msgSender lvrcSent) pk
      lvrcSndrSt  : EventProcessor
      lvrcSndrSt≡ : Map-lookup (msgSender lvrcSent) (peerStates st) ≡ just lvrcSndrSt
      lvrcLvr     : (msgPart lvrcSent) ^∙ vRound ≤ (₋epEC lvrcSndrSt) ^∙ epLastVotedRound
  open LvrCarrier

  firstSendEstablishes : ∀ {e} → Vote → PK → SystemState e → SystemStateRel Step
  firstSendEstablishes _ _ _ (step-epoch _)               = Lift (ℓ+1 0ℓ) ⊥
  firstSendEstablishes _ _ _ (step-peer (step-cheat _ _)) = Lift (ℓ+1 0ℓ) ⊥
  firstSendEstablishes {e} v' pk origSt sysStep@(step-peer {e'} {pid'} {pre = pre} pstep@(step-honest _)) =
                         ( ReachableSystemState pre
                         × ¬ MsgWithSig∈ pk (signature v' unit) (msgPool pre)
                         × LvrCarrier pk (signature v' unit) origSt
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
     with impl-sps-avp {m = msgWhole mws} r hpk x nm∈outs (msg⊆ mws) (msgSigned mws)
  ...| inj₂ sentb4 rewrite msgSameSig mws = ⊥-elim (¬sentb4 sentb4)
  ...| inj₁ (vpk' , _)
     with x
  ...| step-init _ refl = ⊥-elim (¬Any[] nm∈outs)
  ...| step-msg {s' = st} m∈pool ms≡ handle≡
     with sameEpoch⇒sameEC vpk vpk' refl
  ...| refl
     with newVoteSameEpochGreaterRound x ms≡ (msg⊆ mws) nm∈outs (msgSigned mws)
                                       (subst (λ sig → ¬ MsgWithSig∈ pk sig (msgPool pre))
                                              (sym (msgSameSig mws))
                                              ¬sentb4)
  ...| _ , refl , newlvr = r , ¬sentb4
                         , (mkLvrCarrier mws vpk st Map-set-correct (≤-reflexive newlvr))

  LvrCarrier-transp : ∀ {e e' e'' pk sig} {orig : SystemState e} {pre : SystemState e'}{post : SystemState e''}
                     → (theStep : Step pre post)
                     → LvrCarrier pk sig pre
                     → LvrCarrier pk sig post
  LvrCarrier-transp {e} {pre = pre} {post} (step-epoch ec) (mkLvrCarrier mws vpk spre spre≡ lvr) =
    mkLvrCarrier mws (ValidSenderForPK-stable-epoch ec vpk) spre spre≡ lvr
  LvrCarrier-transp {e' = e'} {pre = pre} {post} sp@(step-peer {pid = pid} {st'} {pre = .pre} sps) (mkLvrCarrier mws vpk spre spre≡ lvr)
     with sps
  ...| step-cheat fm isch rewrite cheatStepDNMPeerStates (step-cheat {pre = pre} fm isch) unit =
                  mkLvrCarrier (MsgWithSig∈-++ʳ mws) vpk spre spre≡ (≤-trans lvr (≤-reflexive refl)) -- PeerStates not changed by cheat steps
  ...| step-honest (step-init _ handle≡) = {!!}
                                         -- We cannot prove this yet because
                                         -- initialEventProcessorAndMessages is faked for now.  We
                                         -- need to establish rules for what initialization by a
                                         -- peer pid does.  It must ensure that if pid's new
                                         -- peerState is for epoch e and has lastVotedRound = r,
                                         -- then pid has not previously sent any messages containing
                                         -- votes for the epoch e and for a round higher than r.

  ...| theStep@(step-honest {pid} msgStep@(step-msg {s = s} {s' = s'}{outs = outs} m∈pool ps≡pre handler≡))
     -- If the epoch doesn't change (which it never does, so far), then the lastVotedRound is
     -- monotonically nondecreasing for each honest peer step.
     with Map-lookup (msgSender mws) (peerStates pre) | inspect (Map-lookup (msgSender mws)) (peerStates pre)
  ...| nothing    | _ = ⊥-elim (maybe-⊥ spre≡ refl)
  ...| just spre' | [ R ] rewrite just-injective spre≡
     with peersRemainInitialized (step-peer theStep) R
  ...| spost , spost≡
     with lastVoteRound-mono' (step-peer theStep) R spost≡
  ...| lvrmono = mkLvrCarrier (MsgWithSig∈-++ʳ mws) vpk spost spost≡
                              (≤-trans lvr (lvrmono (noEpochChangeYet (step-peer theStep) R spost≡)))

  LvrCarrier-transp* : ∀ {e e' pk sig} {start : SystemState e}{final : SystemState e'}
                     → LvrCarrier pk sig start
                     → (step* : Step* start final)
                     → LvrCarrier pk sig final
  LvrCarrier-transp* lvrc step-0 = lvrc
  LvrCarrier-transp* {start = start} lvrc (step-s s* s) = LvrCarrier-transp {orig = start} s (LvrCarrier-transp* lvrc s*)

  fSE⇒rnd≤lvr : ∀ {v' pk e'}
              → {final : SystemState e'}
              → Meta-Honest-PK pk
              → ∀ {d d'}{pre : SystemState d} {post : SystemState d'}{theStep : Step pre post}
              → firstSendEstablishes v' pk post theStep
              → (step* : Step* post final)
              → LvrCarrier pk (signature v' unit) final
  fSE⇒rnd≤lvr _ {theStep = step-epoch _} ()
  fSE⇒rnd≤lvr {v' = v'} {pk} hpk {pre = pre} {post} {theStep = step-peer {pid = β} {outs = outs} (step-honest sps)}
              (r , ¬sentb4 , lvrc@(mkLvrCarrier mws vpk spre spre≡ lvr)) step*
              = LvrCarrier-transp* lvrc step* -}

  honMsg∈pool⇒ValidSenderForPK :  ∀ {e pid pid' pk v m}{st : SystemState e}
                               → (r : ReachableSystemState st)
                               → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                               → v ⊂Msg m → (pid' , m) ∈ (msgPool st)
                               → ValidSenderForPK (availEpochs st) v pid pk

  honMsg∈pool⇒pkOwner : ∀ {e pid pid' pk v m}{st : SystemState e}
                      → (r : ReachableSystemState st)
                      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                      → v ⊂Msg m → (pid' , m) ∈ (msgPool st)
                      → ValidSenderForPK (availEpochs st) v pid pk
                      → (pid , m) ∈ (msgPool st)


{-
  oldVoteRound≤lvr :  ∀ {e pid pid' pk v m s}{st : SystemState e}
                    → (r : ReachableSystemState st)
                    → Map-lookup pid (peerStates st) ≡ just s
                    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                    → v ⊂Msg m →  (pid' , m) ∈ (msgPool st)
                    → (₋epEC s) ^∙ epEpoch ≡ (v ^∙ vEpoch)
                    → v ^∙ vRound ≤ (₋epEC s) ^∙ epLastVotedRound
  oldVoteRound≤lvr (step-s {e} {e'} {e''} r (step-epoch _)) lkp≡s pkH sig v⊂m m∈pool ep≡ = {!!}
  oldVoteRound≤lvr {pid = pid} {v = v} {m = m} (step-s r (step-peer cheat@(step-cheat _ _))) lkp≡s pkH sig v⊂m m∈pool ep≡
    with ¬cheatForgeNew cheat refl unit pkH (mkMsgWithSig∈ m v v⊂m pid m∈pool sig refl)
  ...| msb4
    with msgSameSig msb4
  ...| refl
   rewrite cheatStepDNMPeerStates cheat unit
   = let m∈ = msg∈pool msb4
         m∈poolb4 = honMsg∈pool⇒pkOwner r pkH (msgSigned msb4) (msg⊆ msb4) (msg∈pool msb4)
     in oldVoteRound≤lvr r lkp≡s pkH sig {!!} {!m∈poolb4!} {!!}
  oldVoteRound≤lvr (step-s r (step-peer (step-honest {pid} {st} {outs} x))) lkp≡s pkH sig v⊂m m∈pool ep≡ = {!!}
-}

  pid≢⇒msgSent4 : ∀ {e pid pk v} {pid' s' outs}{st : SystemState e}
                → (r : ReachableSystemState st)
                → (stP : StepPeerState pid' (availEpochs st) (msgPool st)
                                       (Map-lookup pid' (peerStates st)) s' outs)
                → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                → MsgWithSig∈ pk (ver-signature sig)
                              (msgPool (StepPeer-post (step-honest stP)))
                → ValidSenderForPK (availEpochs st) v pid pk
                → pid ≢ pid'
                → MsgWithSig∈ pk (ver-signature sig) (msgPool st)

  pid≢DNMState : ∀ {e pid s} {pid' s' outs}{st : SystemState e}
               → (r : ReachableSystemState st)
               → (stP : StepPeerState pid' (availEpochs st) (msgPool st)
                                      (Map-lookup pid' (peerStates st)) s' outs)
               → pid ≢ pid'
               → Map-lookup pid (peerStates (StepPeer-post (step-honest stP))) ≡ just s
               → Map-lookup pid (peerStates st) ≡ just s



  oldVoteRound≤lvr :  ∀ {e pid pk v s}{pre : SystemState e}
         → (r : ReachableSystemState pre)
         → Map-lookup pid (peerStates pre) ≡ just s
         → Meta-Honest-PK pk → (sig : WithVerSig pk v)
         → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
         → ValidSenderForPK (availEpochs pre) v pid pk
         → (₋epEC s) ^∙ epEpoch ≡ (v ^∙ vEpoch)
         → v ^∙ vRound ≤ (₋epEC s) ^∙ epLastVotedRound
  oldVoteRound≤lvr (step-s {e} {e'} {e''} r (step-epoch _)) lkp≡s pkH sig msv vspkv ep≡
      = oldVoteRound≤lvr r lkp≡s pkH sig msv {!!} ep≡
  oldVoteRound≤lvr (step-s r (step-peer cheat@(step-cheat fm ch))) lkp≡s pkH sig msv vspkv ep≡
     with ¬cheatForgeNew cheat refl unit pkH msv
  ...| msb4
     with msgSameSig msb4
  ...| refl
    rewrite cheatStepDNMPeerStates cheat unit
    = oldVoteRound≤lvr r lkp≡s pkH sig msb4 vspkv ep≡

  oldVoteRound≤lvr {pid = pid} {pre = pre} (step-s r step@(step-peer stPeer@(step-honest {pid'} {st} {outs} stP))) lkp≡s pkH sig msv vspkv ep≡
    with pid ≟ pid'
  ...| no imp =  let ms≡pre = pid≢DNMState r stP imp lkp≡s
                     mwssb4 = pid≢⇒msgSent4 r stP pkH sig msv vspkv imp
                    in oldVoteRound≤lvr r ms≡pre pkH sig mwssb4 vspkv ep≡
  ...| yes refl
     with stP
  ...| step-init _ refl = {!!} --oldVoteRound≤lvr r {!lkp≡s!} pkH sig msv vspkv {!!}
                            -- We cannot prove this yet because
                            -- initialEventProcessorAndMessages is faked for now.  We
                            -- need to establish rules for what initialization by a
                            -- peer pid does.  It must ensure that if pid's new
                            -- peerState is for epoch e and has lastVotedRound = r,
                            -- then pid has not previously sent any messages containing
                            -- votes for the epoch e and for a round higher than r
  ...| step-msg {_ , nm} {ms} {s} {s'} m∈pool ms≡ handle≡
      with Any-++⁻ (List-map (pid' ,_) outs) (msg∈pool msv)
  ...| inj₁ m∈outs = {!!}
  ...| inj₂ msb4
    with MsgWithSig∈-transp msv msb4
  ...| mwssb4
    with sameHonestSig⇒sameVoteData pkH sig (msgSigned mwssb4) (sym (msgSameSig mwssb4))
  ...| inj₁ hb = ⊥-elim (PerState.meta-sha256-cr pre (step-s r step) hb)
  ...| inj₂ refl = let ep≡stP  = noEpochChangeYet step ms≡ lkp≡s
                       ep≡Vote = trans ep≡stP ep≡
                       lvr≤ = lastVoteRound-mono' step ms≡ lkp≡s ep≡stP
                   in ≤-trans (oldVoteRound≤lvr r ms≡ pkH sig mwssb4 vspkv ep≡Vote) lvr≤



  vo₁ : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁ r (step-init _ refl) _ _ m∈outs _ _ _ _ _ _ _ _ = ⊥-elim (¬Any[] m∈outs)
  vo₁ {pid' = pid'} r (step-msg {_ , nm} {ms} {s} m∈pool ms≡ hndl≡) {v} {m} {v'} {m'} pkH v⊂m m∈outs sv ¬msb vspkv v'⊂m' m'∈pool sv' ep≡ r≡
    rewrite cong proj₂ hndl≡
    with nm
  ...| P pm
    with m∈outs
  ...| here refl
    with v⊂m
  ... | vote∈vm = let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sv' refl
                      vspkv' = ValidSenderForPK⇒ep≡ sv sv' ep≡ vspkv
                      ep≡stP = trans (epoch≡stepPeer r ms≡) ep≡
                      rv'<rv = oldVoteRound≤lvr r ms≡ pkH sv' m'mwsb vspkv' ep≡stP
                  in ⊥-elim (<⇒≢ (s≤s rv'<rv) (sym r≡))
  ... | vote∈qc vs∈qc v≈rbld (inV qc∈m)
     rewrite cong ₋vSignature v≈rbld
    = ⊥-elim (¬msb (qcVotesSentB4 r ms≡ qc∈m refl vs∈qc))
 
{-
  vo₁ r (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₁ {e} {pid} {pk = pk} {pre = pre} r (step-msg m∈pool ps≡ hndl≡)
      {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 vpb v'⊂m' m'∈pool sig' refl rnds≡
       with newVoteSameEpochGreaterRound {e} {availEpochs pre} {pid}
                                          (step-msg m∈pool ps≡ hndl≡) ps≡ v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the poststate of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of the peer that
     -- sent v'
     with Any-Step-elim {Q = LvrCarrier pk (ver-signature sig') pre}
                        (fSE⇒rnd≤lvr {v'} hpk)
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE hpk ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| mkLvrCarrier mws vpf' sndrst sndrst≡ v'rnd≤lvr
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
                    just-injective (trans (sym ps≡) sndrst≡)
                    -- So we have proved both that the round of v' is ≤ the lastVotedRound of
                    -- the peer's state and that the round of v' is one greater than that value,
                    -- which contradicts the original assumption that they are equal
                    = ⊥-elim (1+n≰n (≤-trans (≤-reflexive suclvr≡v'rnd)
                                             (≤-trans (≤-reflexive rnds≡) v'rnd≤lvr)))
-}

  vo₂ : VO.ImplObligation₂
  vo₂ _ (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₂ {pk = pk} {st} r (step-msg {pid , nm} {s = ps} _ ps≡ hndl≡) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig vnew vpk v'⊂m' m'∈outs sig' v'new vpk' es≡ rnds≡
     rewrite cong proj₂ hndl≡
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
