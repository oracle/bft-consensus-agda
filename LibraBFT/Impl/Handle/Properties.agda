{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module provides some scaffolding to define the handlers for our
-- implementation and connect them to the interface of the SystemModel.

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All


module LibraBFT.Impl.Handle.Properties
  --(bsi : BootstrapInfo)
  where

import      LibraBFT.Impl.Handle as Handle
open        Handle.RealHandler --bsi
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK PeerCanSignForPK-stable

open        Invariants
open        RoundManagerTransProps
import      LibraBFT.Impl.Handle.InitProperties as IP

-- TODO-1: Should 'invariantsCorrect' and direct corollaries be in a `Properties.Invariants` module?
------------------------------------------------------------------------------

-- For any peer in a reachable state, show that it respects RoundManager invariants.
invariantsCorrect
  : ∀ pid (pre : SystemState)
  → initialised pre pid ≡ initd
  → ReachableSystemState pre
  → RoundManagerInv (peerStates pre pid)

--------------------------------------------------
-- AN UNINITIALIZED PEER.
-- A peer has NOT been initialized at 'step-0', therefore it cannot be initialized (i.e., absurd).
invariantsCorrect _ _ () step-0

--------------------------------------------------
-- A CHEATER DOES NOT MODIFY STATE NOR INITIALIZED.
-- pid    : the peer we are reasoning about
-- pid'   : the peer taking the step
--          in the cheat step case, if does not matter if pid == pid'
-- pre    : the prestate of pid
-- pre'   : pre state for this reachable state (before the step, i.e., cheat here)
-- preach : evidence that pre' is reachable
-- cheatStepDNMPeerStates₁  : Does Not Modify state
-- cheatStepDNMInitialised₁ : Does Not Modify initialized
invariantsCorrect pid pre ini (step-s {pre = pre'} preach (step-peer step@(step-cheat  {pid'} _)))
  -- Goal: RoundManagerInv (override (peerStates pre') pid' (peerStates pre' pid') pid)
  rewrite cheatStepDNMPeerStates₁ {pid'} {pid} {pre = pre'} step unit
  -- Goal: RoundManagerInv (peerStates pre' pid)
  with trans (sym $ cheatStepDNMInitialised₁ step unit) ini
...| initialised-pre'-pid≡-initd                        -- preach : ReachableSystemState pre'
  = invariantsCorrect pid pre' initialised-pre'-pid≡-initd preach

--------------------------------------------------
-- Honest steps for the rest of the proof.
-- Note: all these top-level 'invariantsCorrect' are the SAME clause,
-- each with different pattern matching.

--------------------------------------------------
-- PEERS CANNOT MODIFY EACH OTHER'S STATE NOR INITIALIZED STATUS.
-- Reasoning about pid.
-- Peer taking step is different (pid').
invariantsCorrect pid pre ini (step-s {pre = pre'} preach (step-peer step@(step-honest {pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid' -- NO case : step is for a different peer (pid') not this peer (pid).
  -- In that case pid' cannot modify pid's state,
  rewrite sym (pids≢StepDNMPeerStates {pre = pre'} sps pid≢pid')
  -- nor pid's initialized status.
  = invariantsCorrect pid pre' (trans (pids≢StepDNMInitialised {pre = pre'} sps pid≢pid') ini) preach

--------------------------------------------------
-- INITIALIZATION STEP
-- pre' is pre state of this init step
invariantsCorrect pid _   _   (step-s {pre = pre'} preach (step-peer (step-honest {outs = outs} (step-init {rm} handler-pid-bsi-≡-just-rm×outs _))))
   | yes refl -- YES is from the 'with' above
              -- because this is the SAME clause except pattern matching deeper to get 'step-init'.
  -- Goal: RoundManagerInv ... where peerStates pre' pid "contains" the 'rm' from init
  rewrite override-target-≡ {a = pid} {b = rm} {f = peerStates pre'}
  -- Goal: RoundManagerInv rm
  with IP.realHandlerSpec.contract pid fakeBootstrapInfo handler-pid-bsi-≡-just-rm×outs
...| IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts
  = IP.realHandlerSpec.ContractOk.rmInv IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts

--------------------------------------------------
-- PROPOSAL MSG
invariantsCorrect pid _   _   (step-s {pre = pre'} preach (step-peer (step-honest (step-msg {sndr , P pm} m∈pool ini))))
   | yes refl -- pid≡pid'
   -- Goal: RoundManagerInv ... where peerStates pre' pid "contains" the proposal msg
  with handleProposalSpec.contract! 0 pm (msgPool pre') (peerStates pre' pid)
...| c -- contract that says proposal has been handled
  with handleProposalSpec.Contract.rmInv c
...| invPres --   RoundManagerInv (peerStates pre' pid)
             -- → RoundManagerInv where state is updated from proposal message
  with invariantsCorrect pid pre' ini preach
...| ic      --   RoundManagerInv (peerStates pre' pid)
  -- Modify state to contain "results" of handling the proposal.
  rewrite override-target-≡ {a = pid} {b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)} {f = peerStates pre'}
  = invPres ic

--------------------------------------------------
-- VOTE MSG
invariantsCorrect pid _   _   (step-s {pre = pre'} preach (step-peer (step-honest (step-msg {sndr , V vm} m∈pool ini))))
   | yes refl -- pid≡pid'
  with handleVoteSpec.Contract.rmInv $ handleVoteSpec.contract! 0 vm (msgPool pre') (peerStates pre' pid)
...| invPres
  rewrite override-target-≡ {a = pid} {b = LBFT-post (handleVote 0 vm) (peerStates pre' pid)} {f = peerStates pre'}
  = invPres (invariantsCorrect pid pre' ini preach)

--------------------------------------------------
-- COMMIT MSG
invariantsCorrect pid _   _   (step-s {pre = pre'} preach (step-peer (step-honest (step-msg {sndr , C cm} m∈pool ini))))
   | yes refl -- pid≡pid'
  rewrite override-target-≡ {a = pid} {b = LBFT-post (handle pid (C cm) 0) (peerStates pre' pid)} {f = peerStates pre'}
  = invariantsCorrect pid pre' ini preach

------------------------------------------------------------------------------

-- All signatures represented in QCs that are in the RoundManager for each peer
-- have been sent before (i.e., no peer conjures a signature and makes a QC out of it
-- and stores it).
qcVoteSigsSentB4 :
    ∀ pid (st : SystemState)
    → initialised st pid ≡ initd
    → ReachableSystemState st
    → QCProps.SigsForVotes∈Rm-SentB4 (msgPool st) (peerStates st pid)

------------------------------------------------------------------------------

-- Handling any messages preserves the above 'qcVoteSigsSentB4' property.
-- Says this indirectly, via ReachableSystemState
-- then says the property holds after executing a handler from that ReachableSystemState.
-- "preserves"
-- - know it is true in the prestate (from qcVoteSigsSendB4)
-- - proving it's true in the poststate.
handlePreservesSigsB4 :
    ∀ {nm pid pre sndr}
    → initialised pre pid ≡ initd
    → ReachableSystemState pre
    → (sndr , nm) ∈ msgPool pre
    → QCProps.SigsForVotes∈Rm-SentB4 (msgPool pre) (LBFT-post (handle pid nm 0) (peerStates pre pid))
handlePreservesSigsB4 {nm} {pid} {pre} {sndr} ini preach m∈pool {qc} {v} {pk} = hyp
   where
   hPool = msgPool pre
   hPre  = peerStates pre pid

   hPost = LBFT-post (handle pid nm 0) hPre

   qcPost' : (nm' : NetworkMsg) → nm' ≡ nm → QCProps.∈Post⇒∈PreOr (_QC∈NM nm) hPre hPost
   qcPost' (P pm) refl = qcPost
      where open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hPool hPre)
   qcPost' (V vm) refl = qcPost
      where open handleVoteSpec.Contract     (handleVoteSpec.contract!     0 vm hPool hPre)
   qcPost' (C cm) refl qc qc∈pre = Left qc∈pre

   hyp : QCProps.SigForVote∈Rm-SentB4 v pk qc hPost hPool
   hyp qc∈hpPst sig {vs} vs∈qcvs ≈v ¬bootstrap
      with qcPost' nm refl qc qc∈hpPst
   ...| Left qc∈hpPre =
     qcVoteSigsSentB4 pid pre ini preach qc∈hpPre sig vs∈qcvs ≈v ¬bootstrap
   ...| Right qc∈m =
      mkMsgWithSig∈ nm v (vote∈qc vs∈qcvs ≈v qc∈m) sndr m∈pool sig (cong (_^∙ vSignature) ≈v)

------------------------------------------------------------------------------

qcVoteSigsSentB4 pid st ()   step-0

qcVoteSigsSentB4 pid st ini (step-s rss (step-peer {pid'} {pre = pre} step@(step-cheat cmc)))
  rewrite cheatStepDNMPeerStates₁ {pid'} {pid} {pre = pre} step unit
  with trans (sym $ cheatStepDNMInitialised₁ step unit) ini
...| initialised-pre-pid≡-initd
  = QCProps.++-SigsForVote∈Rm-SentB4
      {rm = peerStates pre pid} _ (qcVoteSigsSentB4 pid pre initialised-pre-pid≡-initd rss)

qcVoteSigsSentB4 pid st ini (step-s rss (step-peer {pid'} {pre = pre} (step-honest sps)))
  with pid ≟ pid'

-- DIFFERENT PEER CASE
...| no  pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates {pre = pre} sps pid≢pid')
  = QCProps.++-SigsForVote∈Rm-SentB4
      {rm = peerStates pre pid} _
      (qcVoteSigsSentB4 pid pre (trans (pids≢StepDNMInitialised {pre = pre} sps pid≢pid') ini) rss)
...| yes refl
  with sps

-- INIT CASE
...| step-init {rm} handler-pid-bsi≡just-rm×outs _
  = ret
   where
    ret : QCProps.SigsForVotes∈Rm-SentB4 (msgPool st) (peerStates st pid)
    ret
      with IP.realHandlerSpec.contract pid fakeBootstrapInfo handler-pid-bsi≡just-rm×outs
    ...| IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts
      rewrite override-target-≡ {a = pid} {b = rm} {f = peerStates pre}
      = λ qc∈rm sig vs∈qc rbld≈ ¬bootstrap
        → ⊥-elim $
          ¬bootstrap
          (IP.realHandlerSpec.ContractOk.sigs∈bs
            IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts vs∈qc qc∈rm)

-- MSG CASE
...| step-msg {sndr , nm} m∈pool init
  rewrite override-target-≡ {a = pid} {b = LBFT-post (handle pid nm 0) (peerStates pre pid)} {f = peerStates pre}
  = QCProps.++-SigsForVote∈Rm-SentB4
      {rm = LBFT-post (handle pid nm 0) (peerStates pre pid)} _
      (handlePreservesSigsB4 init rss m∈pool)

------------------------------------------------------------------------------

qcVoteSigsSentB4-sps
  : ∀ pid (pre : SystemState) {s acts}
  → ReachableSystemState pre
  → (StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s , acts))
  → ∀ {qc v pk} → qc QCProps.∈RoundManager s
  → WithVerSig pk v
  → ∀ {vs : Author × Signature} → let (pid , sig) = vs in
    vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
  → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo sig
  → MsgWithSig∈ pk sig (msgPool pre)

qcVoteSigsSentB4-sps pid pre rss (step-init {rm} handler-pid-bsi≡just-rm×outs _) qc∈s sig vs∈qcvs ≈v ¬bootstrap
  with IP.realHandlerSpec.contract pid fakeBootstrapInfo handler-pid-bsi≡just-rm×outs
...| IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts
  rewrite sym $ ++-identityʳ (msgPool pre)
  = QCProps.++-SigsForVote∈Rm-SentB4 {rm = rm} (msgPool pre)
      (λ qc∈rm sig vs∈qc rbld≈ ¬bootstrap
       → ⊥-elim $
           ¬bootstrap
           (IP.realHandlerSpec.ContractOk.sigs∈bs
             IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts vs∈qc qc∈rm))
      qc∈s sig vs∈qcvs ≈v ¬bootstrap

qcVoteSigsSentB4-sps pid pre rss (step-msg {sndr , m} m∈pool ini) {qc} {v} {pk} qc∈s sig {vs} vs∈qcvs ≈v ¬bootstrap
  with m
  -- TODO-2: refactor for DRY
...| P pm = help
  where
    hpPre = peerStates pre pid
    open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm (msgPool pre) hpPre)

    help : MsgWithSig∈ pk (proj₂ vs) (msgPool pre)
    help
      with qcPost qc qc∈s
    ...| Left qc∈pre = qcVoteSigsSentB4 pid pre ini rss qc∈pre sig vs∈qcvs ≈v ¬bootstrap
    ...| Right qc∈pm =
      mkMsgWithSig∈ (P pm) v (vote∈qc vs∈qcvs ≈v qc∈pm) sndr m∈pool sig (cong (_^∙ vSignature) ≈v)

   -- TODO-2: refactor for DRY
...| V vm = help
  where
    hvPre = peerStates pre pid
    open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

    help : MsgWithSig∈ pk (proj₂ vs) (msgPool pre)
    help
      with qcPost qc qc∈s
    ...| Left qc∈pre = qcVoteSigsSentB4 pid pre ini rss qc∈pre sig vs∈qcvs ≈v ¬bootstrap
    ...| Right qc∈vm =
      mkMsgWithSig∈ (V vm) v (vote∈qc vs∈qcvs ≈v qc∈vm) sndr m∈pool sig (cong (_^∙ vSignature) ≈v)

...| C cm = qcVoteSigsSentB4 pid pre ini rss qc∈s sig vs∈qcvs ≈v ¬bootstrap

------------------------------------------------------------------------------

lastVotedRound-mono
  : ∀ pid (pre : SystemState) {ppost} {msgs}
  → ReachableSystemState pre
  → initialised pre pid ≡ initd
  → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (ppost , msgs)
  → peerStates pre pid ≡L ppost at rmEpoch
  → Meta.getLastVoteRound ((peerStates pre pid) ^∙ pssSafetyData-rm)
    ≤
    Meta.getLastVoteRound (ppost                ^∙ pssSafetyData-rm)

lastVotedRound-mono pid pre preach ini (step-init _ uni) epoch≡ =
  case (trans (sym ini) uni) of λ ()

lastVotedRound-mono pid pre {ppost} preach ini₀ (step-msg {_ , m} m∈pool ini₁) epoch≡
  with m
...| P pm rewrite sym $ StepPeer-post-lemma {pre = pre} (step-honest (step-msg m∈pool ini₁)) = help
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpPst  = LBFT-post (handleProposal 0 pm) hpPre
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre

  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre {- hpReq -} )
  open RoundManagerInv (invariantsCorrect pid pre ini₁ preach)

  module VoteOld (lv≡ : hpPre ≡L hpPst at pssSafetyData-rm ∙ sdLastVote) where
    help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
    help = ≡⇒≤ (cong (maybe {B = const ℕ} (_^∙ vRound) 0) lv≡)

  module VoteNew {vote : Vote}
    (lv≡v : just vote ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVote)
    (lvr< : hpPre [ _<_ ]L hpPst at pssSafetyData-rm ∙ sdLastVotedRound)
    (lvr≡ : vote ^∙ vRound ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVotedRound )
   where
    help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
    help = ≤-trans (SafetyDataInv.lvRound≤ ∘ SafetyRulesInv.sdInv $ rmSafetyRulesInv ) (≤-trans (<⇒≤ lvr<) (≡⇒≤ (trans (sym lvr≡) $ cong (maybe {B = const ℕ} (_^∙ vRound) 0) lv≡v)))

  open Invariants
  open Reqs (pm ^∙ pmProposal) (hpPre ^∙ lBlockTree)
  open BlockTreeInv
  open BlockStoreInv
  open RoundManagerInv

  rmi : _
  rmi = invariantsCorrect pid pre ini₁ preach

  help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
  help
    with BlockId-correct? (pm ^∙ pmProposal)
  ...| no ¬validProposal
    = VoteOld.help (cong (_^∙ pssSafetyData-rm ∙ sdLastVote) (proj₁ $ invalidProposal ¬validProposal))
  ...| yes pmIdCorr
    with voteAttemptCorrect pmIdCorr (nohc preach m∈pool pid ini₀ rmi refl pmIdCorr)
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?
    with nvg⊎vgusc
  ...| inj₁  (mkVoteNotGenerated lv≡  lvr≤) = VoteOld.help lv≡
  ...| inj₂  (Voting.mkVoteGeneratedUnsavedCorrect vote (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered))
    with voteSrc
  ...| inj₁  (mkVoteOldGenerated lvr≡ lv≡)  = VoteOld.help lv≡
  ...| inj₂  (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡
  help
     | yes refl
     | Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm _ _ (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) _))) sdEpoch≡?
    with voteSrc
  ...| Left  (mkVoteOldGenerated lvr≡ lv≡)  = VoteOld.help lv≡
  ...| Right (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡

-- Receiving a vote or commit message does not update the last vote
...| V vm = ≡⇒≤ $ cong (maybe (_^∙ vRound) 0 ∘ (_^∙ sdLastVote)) noSDChange
   where
   hvPre = peerStates pre pid
   hvPst = LBFT-post (handle pid (V vm) 0) hvPre

   open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

...| C cm = ≤-refl

------------------------------------------------------------------------------

qcVoteSigsSentB4-handle
  : ∀ pid {pre m s acts}
  → ReachableSystemState pre
  → (StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s , acts))
  → send m ∈ acts
  → ∀ {qc v pk}
  → qc QC∈NM m
  → WithVerSig pk v
  → ∀ {vs : Author × Signature} → let (pid , sig) = vs in vs ∈ qcVotes qc
  → rebuildVote qc vs ≈Vote v
  → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo sig
  → MsgWithSig∈ pk sig (msgPool pre)

qcVoteSigsSentB4-handle pid {pre} {m} {s} {acts} preach
                        (step-init handler-pid-bsi≡just-rm×outs _)
                        send∈acts
                        {qc}
                        qc∈m sig vs∈qc v≈rbld ¬bootstrap
  with IP.realHandlerSpec.contract pid fakeBootstrapInfo handler-pid-bsi≡just-rm×outs
...| IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts
  = obm-dangerous-magic' "⊥-elim $ ¬bootstrap (IP.realHandlerSpec.ContractOk.sigs∈bs IP-realHandlerSpec-ContractOk-pid-bsi-rm-acts vs∈qc {!!} {-qc∈m-})"

qcVoteSigsSentB4-handle pid {pre} {m} {s} {acts} preach
                        sps@(step-msg {_ , nm} m∈pool ini)
                        m∈acts
                        {qc} qc∈m sig vs∈qc v≈rbld ¬bootstrap =
  qcVoteSigsSentB4-sps pid pre preach sps qc∈rm sig vs∈qc v≈rbld ¬bootstrap
 where
  hdPool = msgPool pre
  hdPre  = peerStates pre pid
  hdPst  = LBFT-post (handle pid nm 0) hdPre
  hdOut  = LBFT-outs (handle pid nm 0) hdPre

  qc∈rm : qc QCProps.∈RoundManager hdPst
  qc∈rm
    with sendMsg∈actions {hdOut} {st = hdPre} m∈acts
  ...| out , out∈hdOut , m∈out = All-lookup (outQcs∈RM1 nm refl) out∈hdOut qc m qc∈m m∈out
   where
    outQcs∈RM1 : (nm' : NetworkMsg) → nm ≡ nm' → QCProps.OutputQc∈RoundManager hdOut hdPst
    outQcs∈RM1 (P pm) refl = outQcs∈RM
     where open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hdPool hdPre)
    outQcs∈RM1 (V vm) refl = outQcs∈RM
     where open handleVoteSpec.Contract     (handleVoteSpec.contract!     0 vm hdPool hdPre)
