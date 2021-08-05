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

open import LibraBFT.Impl.Handle
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.Handle.Properties where

postulate -- TODO-2: prove (waiting on: `initRM`)
  initRM-correct : RoundManager-correct initRM
  initRM-qcs     : QCProps.SigsForVotes∈Rm-SentB4 [] initRM -- NOTE: all QCs in `initRM` come from the genesis info
  initRM-btInv   : BlockStoreInv initRM

initRMSatisfiesInv : RoundManagerInv [] initRM
initRMSatisfiesInv =
  RoundManagerInvariants.mkRoundManagerInv initRM-correct initRM-qcs refl initRM-btInv
    (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))

invariantsCorrect -- TODO-1: Decide whether this and direct corollaries should live in a `Properties.Invariants` module
  : ∀ pid (pre : SystemState)
    → (preach : ReachableSystemState pre) → RoundManagerInv (Step*-prev-msgPool preach) (peerStates pre pid)
invariantsCorrect pid pre@._ step-0 = initRMSatisfiesInv

invariantsCorrect pid _ (step-s{pre = pre'} preach' (step-peer (step-cheat{pid = pid'} cmc)))
  rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre'} (step-cheat{pre'} cmc) unit
  |       Step*-prev-msgPool-lemma₁{st₂ = pre'} preach'
  = ++-RoundManagerInv _ (invariantsCorrect pid pre' preach')

invariantsCorrect pid _ (step-s{pre = pre'} preach' (step-peer (step-honest{pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates{pre = pre'} sps pid≢pid')
  |       Step*-prev-msgPool-lemma₁{st₂ = pre'} preach'
  = ++-RoundManagerInv _ (invariantsCorrect pid pre' preach')
invariantsCorrect pid _ (step-s{pre = pre'} preach (step-peer (step-honest (step-init ini))))
   | yes refl
  rewrite override-target-≡{a = pid}{b = initRM}{f = peerStates pre'}
   |      sym $ ++-identityʳ (msgPool pre')
   |      Step*-prev-msgPool-lemma₁{st₂ = pre'} preach
   = ++-RoundManagerInv _ initRMSatisfiesInv
invariantsCorrect pid _ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , P pm} m∈pool ini))))
   | yes refl
  with handleProposalSpec.Contract.rmInv $ handleProposalSpec.contract! 0 pm (msgPool pre') (peerStates pre' pid)
...| invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  |       Step*-prev-msgPool-lemma₁{st₂ = pre'} preach
  = invPres (++-RoundManagerInv _ (invariantsCorrect pid pre' preach))
invariantsCorrect pid _ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , V vm} m∈pool ini))))
   | yes refl
  with handleVoteSpec.Contract.rmInv $ handleVoteSpec.contract! 0 vm (msgPool pre') (peerStates pre' pid)
...| invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleVote 0 vm) (peerStates pre' pid)}{f = peerStates pre'}
  |       Step*-prev-msgPool-lemma₁{st₂ = pre'} preach
  = invPres (++-RoundManagerInv _ (invariantsCorrect pid pre' preach))

invariantsCorrect pid pre@._ preach'@(step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , C x} m∈pool ini))))
   | yes refl = TODO
  where
  postulate -- TODO-3: prove (waiting on: `handle`)
    TODO : RoundManagerInv (Step*-prev-msgPool preach') (peerStates pre pid)

qcVoteSigsSentB4
  : ∀ pid (pre : SystemState) {ppost msgs}
    → ReachableSystemState pre
    → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (ppost , msgs)
    → ∀ {v qc vs pk}
    → qc QCProps.∈RoundManager ppost
    → vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
    → WithVerSig pk v
    → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
    → MsgWithSig∈ pk (proj₂ vs) (msgPool pre)
qcVoteSigsSentB4 pid st {ppost} rss sps{qc = qc} qc∈rm vs∈qcvs ≈v sig ¬gen
  = qcsigsSentB4 qc∈rm' sig vs∈qcvs ≈v ¬gen
  where
  open RoundManagerInv (invariantsCorrect pid _ (step-s rss (step-peer (step-honest sps))))

  qc∈rm' : qc QCProps.∈RoundManager (peerStates (StepPeer-post{pre = st} (step-honest sps)) pid)
  qc∈rm' rewrite override-target-≡{a = pid}{b = ppost}{f = peerStates st} = qc∈rm

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
...| P pm rewrite sym $ StepPeer-post-lemma{pre = pre} (step-honest (step-msg m∈pool ini₁)) = help
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpPst  = LBFT-post (handleProposal 0 pm) hpPre
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre

  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre)
  open RoundManagerInvariants.RoundManagerInv (invariantsCorrect pid pre preach)

  module VoteOld (lv≡ : hpPre ≡L hpPst at pssSafetyData-rm ∙ sdLastVote) where
    help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
    help = ≡⇒≤ (cong (maybe{B = const ℕ} (_^∙ vRound) 0) lv≡)

  module VoteNew {vote : Vote}
    (lv≡v : just vote ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVote)
    (lvr< : hpPre [ _<_ ]L hpPst at pssSafetyData-rm ∙ sdLastVotedRound)
    (lvr≡ : vote ^∙ vRound ≡ hpPst ^∙ pssSafetyData-rm ∙ sdLastVotedRound )
    where
    help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
    help = ≤-trans (SafetyDataInv.lvRound≤ ∘ SafetyRulesInv.sdInv $ srInv ) (≤-trans (<⇒≤ lvr<) (≡⇒≤ (trans (sym lvr≡) $ cong (maybe {B = const ℕ} (_^∙ vRound) 0) lv≡v)))

  help : Meta.getLastVoteRound hpPre ≤ Meta.getLastVoteRound hpPst
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

...| C cm = ≡⇒≤ TODO
  where
  postulate -- TODO-2: prove (waiting on: `handle`)
    TODO : Meta.getLastVoteRound (peerStates pre pid) ≡ Meta.getLastVoteRound (LBFT-post (handle pid (C cm) 0) (peerStates pre pid))
