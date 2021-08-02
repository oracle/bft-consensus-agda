{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

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
open import LibraBFT.Impl.Properties.Common
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Impl.Handle
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

open RoundManagerInvariants
open RoundManagerTransProps
open ReachableSystemStateProps

module LibraBFT.Impl.Handle.Properties where

postulate -- TODO-2: prove (waiting on: `initRM`)
  initRM-correct : RoundManager-correct initRM
  initRM-qcs     : QCProps.SigsForVotes∈Rm-SentB4 [] initRM -- TODO-1: This is not true (the definition of the predicate needs updating).
  initRM-btInv   : BlockStoreInv initRM

initRMSatisfiesInv : RoundManagerInvariants.RoundManagerInv [] initRM
initRMSatisfiesInv =
  RoundManagerInvariants.mkRoundManagerInv initRM-correct initRM-qcs refl initRM-btInv
    (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))

invariantsCorrect
  : ∀ pid (pre : SystemState)
    → ReachableSystemState pre → RoundManagerInv (msgPool pre) (peerStates pre pid)
invariantsCorrect pid pre@._ step-0 = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-cheat{pid'} cheatMsgConstraint)))
  rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre'} step unit
  = {!!} -- invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates{pre = pre'} sps pid≢pid')
  = {!!} -- invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-init ini)))) | yes refl
  rewrite override-target-≡{a = pid}{b = initRM}{f = peerStates pre'}
  = {!!} --initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , P pm} m∈pool ini)))) | yes refl
  with handleProposalSpec.contract!-RoundManagerInv 0 pm (msgPool pre') (peerStates pre' pid) (handleProposalRequirements preach m∈pool ini)
... | invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  = {!!} -- invPres (invariantsCorrect pid pre' preach)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , V x} m∈pool ini)))) | yes refl = TODO
  where
  postulate -- TODO-3: prove (waiting on: `handle`)
    TODO : {!!} -- RoundManagerInv (peerStates pre pid)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , C x} m∈pool ini)))) | yes refl = TODO
  where
  postulate -- TODO-3: prove (waiting on: `handle`)
    TODO : RoundManagerInv (msgPool pre) (peerStates pre pid)

lastVotedRound-mono
  : ∀ pid (pre : SystemState) {ppost} {msgs}
    → ReachableSystemState pre
    → initialised pre pid ≡ initd
    → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (ppost , msgs)
    → peerStates pre pid ≡L ppost at rmEpoch
    → Meta.getLastVoteRound (peerStates pre pid) ≤ Meta.getLastVoteRound ppost
lastVotedRound-mono pid pre preach ini (step-init       ini₁) epoch≡ =
  case (trans (sym ini) ini₁) of λ ()
lastVotedRound-mono pid pre{ppost} preach ini (step-msg{_ , m} m∈pool ini₁) epoch≡
  with m
... | P pm rewrite sym $ StepPeer-post-lemma{pre = pre} (step-honest (step-msg m∈pool ini₁)) = help
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpPst  = LBFT-post (handleProposal 0 pm) hpPre
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre

  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre (handleProposalRequirements preach m∈pool ini))
  open RoundManagerInvariants.RoundManagerInv (invariantsCorrect pid pre preach)

  module VoteOld (lv≡ : hpPre ≡L hpPst at pssSafetyData-rm ∙ sdLastVote) where
    help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
    help = ≡⇒≤ (cong (maybe{B = const ℕ} (_^∙ vRound) 0) lv≡)

  module VoteNew
    {vote : Vote} (lv≡v : just vote ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVote) (lvr< : hpPre [ _<_ ]L hpPst at pssSafetyData-rm ∙ sdLastVotedRound)
    (lvr≡ : vote ^∙ vRound ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVotedRound )
    where
    help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
    help = ≤-trans (SafetyDataInv.lvRound≤ ∘ SafetyRulesInv.sdInv $ srInv ) (≤-trans (<⇒≤ lvr<) (≡⇒≤ (trans (sym lvr≡) $ cong (maybe {B = const ℕ} (_^∙ vRound) 0) lv≡v)))

  help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
  help
    with voteAttemptCorrect
  ...  | Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?
    with nvg⊎vgusc
  ... | inj₁ (mkVoteNotGenerated lv≡ lvr≤) = VoteOld.help lv≡
  ... | inj₂ (Voting.mkVoteGeneratedUnsavedCorrect vote (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered))
    with voteSrc
  ... | inj₁ (mkVoteOldGenerated lvr≡ lv≡) = VoteOld.help lv≡
  ... | inj₂ (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡
  help | Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm _ _ (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) _))) sdEpoch≡?
    with voteSrc
  ... | Left (mkVoteOldGenerated lvr≡ lv≡) = VoteOld.help lv≡
  ... | Right (mkVoteNewGenerated lvr< lvr≡) = VoteNew.help lv≡v lvr< lvr≡

-- Receiving a vote or commit message does not update the last vote
... | V vm = ≡⇒≤ TODO
  where
  postulate -- TODO-2: prove (waiting on: `handle`)
    TODO : Meta.getLastVoteRound (peerStates pre pid) ≡ Meta.getLastVoteRound (LBFT-post (handle pid (V vm) 0) (peerStates pre pid))
... | C cm = ≡⇒≤ TODO
  where
  postulate -- TODO-2: prove (waiting on: `handle`)
    TODO : Meta.getLastVoteRound (peerStates pre pid) ≡ Meta.getLastVoteRound (LBFT-post (handle pid (C cm) 0) (peerStates pre pid))
