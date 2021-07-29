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
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK

open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

open StateInvariants
open StateTransProps

module LibraBFT.Impl.Handle.Properties where

-- We can prove this easily for the Agda model because (unlike the Haskell
-- prototype) it does not yet do epoch changes, so only the initial EC is
-- relevant. Later, this will require us to use the fact that epoch changes
-- require proof of committing an epoch-changing transaction.
availEpochsConsistent :
   ∀{pid pid' v v' pk}{st : SystemState}
   → (pkvpf  : PeerCanSignForPK st v  pid  pk)
   → (pkvpf' : PeerCanSignForPK st v' pid' pk)
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → pcs4𝓔 pkvpf ≡ pcs4𝓔 pkvpf'
availEpochsConsistent (mkPCS4PK _ (inGenInfo refl) _) (mkPCS4PK _ (inGenInfo refl) _) refl = refl

postulate -- TODO-2: prove (waiting on: `initRM`)
  initRM-correct : RoundManager-correct initRM
  initRM-btInv   : BlockStoreInv initRM

initRMSatisfiesInv : StateInvariants.RoundManagerInv initRM
initRMSatisfiesInv =
  StateInvariants.mkRoundManagerInv initRM-correct refl initRM-btInv
    (mkSafetyRulesInv (mkSafetyDataInv refl z≤n))

invariantsCorrect
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
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-init ini)))) | yes refl
  rewrite override-target-≡{a = pid}{b = initRM}{f = peerStates pre'}
  = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , P pm} m∈pool ini)))) | yes refl
  with handleProposalSpec.contract!-RoundManagerInv 0 pm (peerStates pre' pid)
... | invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  = invPres (invariantsCorrect pid pre' preach)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , V x} m∈pool ini)))) | yes refl = TODO
  where
  postulate -- TODO-3: prove (waiting on: `handle`)
    TODO : RoundManagerInv (peerStates pre pid)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{sndr , C x} m∈pool ini)))) | yes refl = TODO
  where
  postulate -- TODO-3: prove (waiting on: `handle`)
    TODO : RoundManagerInv (peerStates pre pid)

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
  hpPre = peerStates pre pid
  hpPst = LBFT-post (handleProposal 0 pm) hpPre
  hpOut = LBFT-outs (handleProposal 0 pm) hpPre

  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPre)
  open StateInvariants.RoundManagerInv (invariantsCorrect pid pre preach)

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

postulate -- TODO-3: prove (note: advanced; waiting on: `handle`)
  -- This will require updates to the existing proofs for the peer handlers. We
  -- will need to show that honest peers sign things only for their only PK, and
  -- that they either resend messages signed before or if sending a new one,
  -- that signature hasn't been sent before
  impl-sps-avp : StepPeerState-AllValidParts
