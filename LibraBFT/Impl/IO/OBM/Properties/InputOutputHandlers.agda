{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers where

module epvvSpec where

  contract
    : ∀ pre Post
      → let ep = pre ^∙ lSafetyData ∙ sdEpoch
            vv = (_rmEC pre) ^∙ rmEpochState ∙ esVerifier in
        (Post (ep , vv) pre [])
      → LBFT-weakestPre epvv Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl = pf

module handleProposalSpec (now : Instant) (pm : ProposalMsg) where

  open handleProposal now pm

  epoch = pm ^∙ pmProposal ∙ bEpoch
  round = pm ^∙ pmProposal ∙ bRound

  VoteMsg⊎VoteNotSaved-sdEpoch
    : (pre post : RoundManager) (outs : List Output)
      → NoVote⊎VoteMsgOutsCorrect pre post outs epoch round
      → Set
  VoteMsg⊎VoteNotSaved-sdEpoch pre post outs (Left (strict? , mkNoVoteMsgOutsCorrect noVoteOuts (Left _))) =
    ⊤
  VoteMsg⊎VoteNotSaved-sdEpoch pre post outs (Left (strict? , mkNoVoteMsgOutsCorrect noVoteOuts (Right _))) =
    pre ^∙ lSafetyData ∙ sdEpoch ≡ epoch
  VoteMsg⊎VoteNotSaved-sdEpoch pre post outs (Right _) =
    pre ^∙ lSafetyData ∙ sdEpoch ≡ epoch

  record Contract (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noEpochChange : NoEpochChange pre post
      outsCorrect   : NoVote⊎VoteMsgOutsCorrect pre post outs epoch round
      sdEpoch≡      : VoteMsg⊎VoteNotSaved-sdEpoch pre post outs outsCorrect

  contract : ∀ pre → LBFT-weakestPre (handleProposal now pm) (Contract pre) pre
  contract pre =
    epvvSpec.contract pre (RWST-weakestPre-bindPost unit (λ where (myEpoch , vv) → step₁ myEpoch vv) (Contract pre))
      λ where
        ._ refl →
          (λ where
            (Left _)  eq → contractBail _ refl
            (Right _) eq → contractBail _ refl)
          , λ where
              unit eq →
                processProposalMsgMSpec.contract now pm pre (Contract pre) (pf eq)
    where
    contractBail : ∀ outs → NoVoteOuts outs → Contract pre unit pre outs
    contractBail outs noVoteOuts =
      mkContract reflNoEpochChange (Left (true , mkNoVoteMsgOutsCorrect noVoteOuts (Left reflNoVoteCorrect))) tt

    myEpoch = pre ^∙ lSafetyData ∙ sdEpoch
    vv      = _rmEC pre ^∙ rmEpochState ∙ esVerifier

    ProcessProposalOk = processProposal pm myEpoch vv ≡ Right unit

    epoch≡ : ProcessProposalOk → pre ^∙ lSafetyData ∙ sdEpoch ≡ epoch
    epoch≡ eq
       with processProposalSpec.contract pm myEpoch vv
    ...| con
       rewrite eq = sym con

    pf : ProcessProposalOk → RWST-Post-⇒ (processProposalMsgMSpec.Contract now pm pre) (Contract pre)
    pf ppo r st outs (processProposalMsgMSpec.mkContract inv nv⊎vmoc@(Left (strict? , mkNoVoteMsgOutsCorrect noVoteOuts (Left noVoteCorrect)))) =
      mkContract inv nv⊎vmoc tt
    pf ppo r st outs (processProposalMsgMSpec.mkContract inv nv⊎vmoc@(Left (strict? , mkNoVoteMsgOutsCorrect noVoteOuts (Right voteNotSaved)))) =
      mkContract inv nv⊎vmoc (epoch≡ ppo)
    pf ppo r st outs (processProposalMsgMSpec.mkContract inv nv⊎vmoc@(Right voteMsgOutsCorrect)) =
      mkContract inv nv⊎vmoc (epoch≡ ppo)

  contract! : ∀ pre → LBFT-Post-True (Contract pre) (handleProposal now pm) pre
  contract! pre = LBFT-contract (handleProposal now pm) (Contract pre) pre (contract pre)

  contract!-NoEpochChange : ∀ pre → LBFT-Post-True (λ r st outs → NoEpochChange pre st) (handleProposal now pm) pre
  contract!-NoEpochChange pre = Contract.noEpochChange (contract! pre)
