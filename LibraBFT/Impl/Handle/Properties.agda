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

import      LibraBFT.Impl.Handle as Handle
open        ParamsWithInitAndHandlers Handle.fakeInitAndHandlers
open        PeerCanSignForPK
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms Handle.fakeInitAndHandlers PeerCanSignForPK PeerCanSignForPK-stable

open Invariants
open RoundManagerTransProps

-- TODO-2 : pass in RoundManager (instead of using 'initRM')
-- and the proof that the RoundManager is valid.
module LibraBFT.Impl.Handle.Properties where

postulate -- TODO-2: prove (waiting on: `initRM`)
  initRM-correct  : ValidatorVerifier-correct (Handle.fakeInitRM  ^∙ rmValidatorVerifer)
  initRM-btInv    : BlockTreeInv (rm→BlockTree-EC Handle.fakeInitRM)
  initRM-qcs      : QCProps.SigsForVotes∈Rm-SentB4 [] Handle.fakeInitRM

initRMSatisfiesInv : RoundManagerInv Handle.fakeInitRM
initRMSatisfiesInv =
  mkRoundManagerInv initRM-correct refl initRM-btInv
    (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))

invariantsCorrect -- TODO-1: Decide whether this and direct corollaries should live in an `Properties.Invariants` module
  : ∀ pid (pre : SystemState)
    → ReachableSystemState pre → RoundManagerInv (peerStates pre pid)
invariantsCorrect pid pre@._ step-0 = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-cheat{pid'} cheatMsgConstraint)))
  rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre'} step unit
  = invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates{pre = pre'} sps pid≢pid')
  = invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-init ini))))
   | yes refl
  rewrite override-target-≡{a = pid}{b = Handle.fakeInitRM}{f = peerStates pre'}
   |       sym $ ++-identityʳ (msgPool pre')
   = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , P pm} m∈pool ini))))
   | yes refl
   with handleProposalSpec.Contract.rmInv $ handleProposalSpec.contract! 0 pm (msgPool pre') (peerStates pre' pid)
...| invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  = invPres (invariantsCorrect pid pre' preach)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , V vm} m∈pool ini))))
   | yes refl
  with handleVoteSpec.Contract.rmInv $ handleVoteSpec.contract! 0 vm (msgPool pre') (peerStates pre' pid)
...| invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleVote 0 vm) (peerStates pre' pid)}{f = peerStates pre'}
  = invPres (invariantsCorrect pid pre' preach)

invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , C cm} m∈pool ini))))
   | yes refl
   rewrite override-target-≡{a = pid}{b = LBFT-post (handle pid (C cm) 0) (peerStates pre' pid)}{f = peerStates pre'}
   = invariantsCorrect pid pre' preach

qcVoteSigsSentB4 :
    ∀ pid (st : SystemState)
    → ReachableSystemState st
    → QCProps.SigsForVotes∈Rm-SentB4 (msgPool st) (peerStates st pid)

handlePreservesSigsB4 :
    ∀ {nm pid pre sndr}
    → ReachableSystemState pre
    → (sndr , nm) ∈ msgPool pre
    → QCProps.SigsForVotes∈Rm-SentB4 (msgPool pre) (LBFT-post (handle pid nm 0) (peerStates pre pid))
handlePreservesSigsB4 {nm} {pid} {pre} {sndr} preach m∈pool {qc} {v} {pk} = hyp
   where
   hPool = msgPool pre
   hPre  = peerStates pre pid

   hPost = LBFT-post (handle pid nm 0) hPre

   qcPost' : (nm' : NetworkMsg) → nm' ≡ nm → QCProps.∈Post⇒∈PreOr (_QC∈NM nm) hPre hPost
   qcPost' (P pm) refl = qcPost
      where open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hPool hPre)
   qcPost' (V vm) refl = qcPost
      where open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm hPool hPre)
   qcPost' (C cm) refl qc qc∈pre = Left qc∈pre

   hyp : QCProps.SigForVote∈Rm-SentB4 v pk qc hPost hPool
   hyp qc∈hpPst sig {vs} vs∈qcvs ≈v ¬gen
      with qcPost' nm refl qc qc∈hpPst
   ...| Left qc∈hpPre =
     qcVoteSigsSentB4 pid pre preach qc∈hpPre sig vs∈qcvs ≈v ¬gen
   ...| Right qc∈m =
      mkMsgWithSig∈ nm v (vote∈qc vs∈qcvs ≈v qc∈m) sndr m∈pool sig (cong (_^∙ vSignature) ≈v)

qcVoteSigsSentB4 pid st step-0 = initRM-qcs
qcVoteSigsSentB4 pid st (step-s rss (step-peer{pid'}{pre = pre} step@(step-cheat cmc)))
   rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre} step unit
   = QCProps.++-SigsForVote∈Rm-SentB4{rm = peerStates pre pid} _ (qcVoteSigsSentB4 pid pre rss)
qcVoteSigsSentB4 pid st (step-s rss (step-peer{pid'}{pre = pre} (step-honest sps)))
   with pid ≟ pid'
...| no  pid≢
     rewrite sym (pids≢StepDNMPeerStates{pre = pre} sps pid≢)
     = QCProps.++-SigsForVote∈Rm-SentB4{rm = peerStates pre pid} _ (qcVoteSigsSentB4 pid pre rss)
...| yes refl
   with sps
...| step-init uni
   = ret
   where
   ret : QCProps.SigsForVotes∈Rm-SentB4 (msgPool st) (peerStates st pid)
   ret rewrite override-target-≡{a = pid}{b = Handle.fakeInitRM}{f = peerStates pre}
       |       sym $ ++-identityʳ (msgPool pre)
       = QCProps.++-SigsForVote∈Rm-SentB4{rm = Handle.fakeInitRM} (msgPool pre) initRM-qcs
...| step-msg{sndr , nm} m∈pool init
   rewrite override-target-≡{a = pid}{b = LBFT-post (handle pid nm 0) (peerStates pre pid)} {f = peerStates pre}
   = QCProps.++-SigsForVote∈Rm-SentB4 {rm = LBFT-post (handle pid nm 0) (peerStates pre pid)} _ (handlePreservesSigsB4 rss m∈pool)

qcVoteSigsSentB4-sps
  : ∀ pid (pre : SystemState) {s acts}
    → ReachableSystemState pre
    → (StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (just (s , acts)))
    → ∀ {qc v pk} → qc QCProps.∈RoundManager s
    → WithVerSig pk v
    → ∀ {vs : Author × Signature} → let (pid , sig) = vs in
      vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
    → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo sig
    → MsgWithSig∈ pk sig (msgPool pre)
qcVoteSigsSentB4-sps pid pre rss (step-init uni) qc∈s sig vs∈qcvs ≈v ¬gen
   rewrite sym $ ++-identityʳ (msgPool pre)
   = QCProps.++-SigsForVote∈Rm-SentB4{rm = Handle.fakeInitRM} (msgPool pre) initRM-qcs qc∈s sig vs∈qcvs ≈v ¬gen
qcVoteSigsSentB4-sps pid pre rss (step-msg{sndr , m} m∈pool ini) {qc}{v}{pk} qc∈s sig {vs} vs∈qcvs ≈v ¬gen
   with m
   -- TODO-2: refactor for DRY
...| P pm = help
   where
   hpPre = peerStates pre pid
   open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm (msgPool pre) hpPre)

   help : MsgWithSig∈ pk (proj₂ vs) (msgPool pre)
   help
      with qcPost qc qc∈s
   ...| Left qc∈pre = qcVoteSigsSentB4 pid pre rss qc∈pre sig vs∈qcvs ≈v ¬gen
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
   ...| Left qc∈pre = qcVoteSigsSentB4 pid pre rss qc∈pre sig vs∈qcvs ≈v ¬gen
   ...| Right qc∈vm =
     mkMsgWithSig∈ (V vm) v (vote∈qc vs∈qcvs ≈v qc∈vm) sndr m∈pool sig (cong (_^∙ vSignature) ≈v)

...| C cm = qcVoteSigsSentB4 pid pre rss qc∈s sig vs∈qcvs ≈v ¬gen

lastVotedRound-mono
  : ∀ pid (pre : SystemState) {ppost} {msgs}
    → ReachableSystemState pre
    → initialised pre pid ≡ initd
    → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (just (ppost , msgs))
    → peerStates pre pid ≡L ppost at rmEpoch
    → Meta.getLastVoteRound ((peerStates pre pid) ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (ppost ^∙ pssSafetyData-rm)
lastVotedRound-mono pid pre preach ini (step-init       ini₁) epoch≡ =
  case (trans (sym ini) ini₁) of λ ()
lastVotedRound-mono pid pre{ppost} preach ini (step-msg{_ , m} m∈pool ini₁) epoch≡
  with m
...| P pm rewrite sym $ StepPeer-post-lemma{pre = pre} (step-honest (step-msg m∈pool ini₁)) = help
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpPst  = LBFT-post (handleProposal 0 pm) hpPre
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre

  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre {- hpReq -} )
  open RoundManagerInv (invariantsCorrect pid pre preach)

  module VoteOld (lv≡ : hpPre ≡L hpPst at pssSafetyData-rm ∙ sdLastVote) where
    help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
    help = ≡⇒≤ (cong (maybe{B = const ℕ} (_^∙ vRound) 0) lv≡)

  module VoteNew {vote : Vote}
    (lv≡v : just vote ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVote)
    (lvr< : hpPre [ _<_ ]L hpPst at pssSafetyData-rm ∙ sdLastVotedRound)
    (lvr≡ : vote ^∙ vRound ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVotedRound )
    where
    help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
    help = ≤-trans (SafetyDataInv.lvRound≤ ∘ SafetyRulesInv.sdInv $ rmSafetyRulesInv ) (≤-trans (<⇒≤ lvr<) (≡⇒≤ (trans (sym lvr≡) $ cong (maybe {B = const ℕ} (_^∙ vRound) 0) lv≡v)))

  help : Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound (hpPst ^∙ pssSafetyData-rm)
  help
    with voteAttemptCorrect
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?
    with nvg⊎vgusc
  ...| inj₁ (mkVoteNotGenerated lv≡ lvr≤) = VoteOld.help lv≡
  ...| inj₂ (Voting.mkVoteGeneratedUnsavedCorrect vote (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered))
    with voteSrc
  ...| inj₁ (mkVoteOldGenerated lvr≡ lv≡) = VoteOld.help lv≡
  ...| inj₂ (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡
  help
     | Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm _ _ (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) _))) sdEpoch≡?
    with voteSrc
  ...| Left (mkVoteOldGenerated lvr≡ lv≡) = VoteOld.help lv≡
  ...| Right (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡

-- Receiving a vote or commit message does not update the last vote
...| V vm = ≡⇒≤ $ cong (maybe (_^∙ vRound) 0 ∘ (_^∙ sdLastVote)) noSDChange
   where
   hvPre = peerStates pre pid
   hvPst = LBFT-post (handle pid (V vm) 0) hvPre

   open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

...| C cm = ≤-refl

qcVoteSigsSentB4-handle
    : ∀ pid {pre m s acts}
    → ReachableSystemState pre
    → (StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (just (s , acts)))
    → send m ∈ acts
    → ∀ {qc v pk} → qc QC∈NM m
    → WithVerSig pk v
    → ∀ {vs : Author × Signature} → let (pid , sig) = vs in
      vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
    → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo sig
    → MsgWithSig∈ pk sig (msgPool pre)
qcVoteSigsSentB4-handle pid {pre} {m} {s} {acts} preach sps@(step-init ini) ()
qcVoteSigsSentB4-handle pid {pre} {m} {s} {acts} preach sps@(step-msg {_ , nm} m∈pool ini) m∈acts {qc} qc∈m sig vs∈qc v≈rbld ¬gen =
  qcVoteSigsSentB4-sps pid pre preach sps qc∈rm sig vs∈qc v≈rbld ¬gen
    where
   hdPool = msgPool pre
   hdPre  = peerStates pre pid
   hdPst  = LBFT-post (handle pid nm 0) hdPre
   hdOut  = LBFT-outs (handle pid nm 0) hdPre

   qc∈rm : qc QCProps.∈RoundManager hdPst
   qc∈rm
      with sendMsg∈actions{hdOut}{st = hdPre} m∈acts
   ...| out , out∈hdOut , m∈out = All-lookup (outQcs∈RM1 nm refl) out∈hdOut qc m qc∈m m∈out
      where
        outQcs∈RM1 : (nm' : NetworkMsg) → nm ≡ nm' → QCProps.OutputQc∈RoundManager hdOut hdPst
        outQcs∈RM1 (P pm) refl = outQcs∈RM
          where open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hdPool hdPre)
        outQcs∈RM1 (V vm) refl = outQcs∈RM
          where open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm hdPool hdPre)
