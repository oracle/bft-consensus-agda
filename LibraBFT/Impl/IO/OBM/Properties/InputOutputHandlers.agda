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

module handleProposalSpec (now : Instant) (pm : ProposalMsg) where

  epoch = pm ^∙ pmProposal ∙ bEpoch
  round = pm ^∙ pmProposal ∙ bRound

  record NoVoteOutsCorrect (pre post : RoundManager) (outs : List Output) : Set where
    constructor mkNoOutsCorrect
    field
      noVoteOuts : NoVoteOuts outs
      nvc⊎vns    : NoVoteCorrect pre post ⊎ VoteNotSaved pre post epoch round

  record VoteMsgOutsCorrect (pre post : RoundManager) (outs : List Output)  : Set where
    constructor mkVoteMsgOutsCorrect
    field
      vm          : VoteMsg
      pid         : Author
      voteMsgOuts : VoteMsgOuts outs vm (pid ∷ [])
      outCorrect  : VoteCorrect pre post epoch round (vm ^∙ vmVote)
      sdEpoch≡    : pre ^∙ lSafetyData ∙ sdEpoch ≡ epoch

  OutsCorrect : (pre post : RoundManager) (outs : List Output) → Set
  OutsCorrect pre post outs = NoVoteOutsCorrect pre post outs ⊎ VoteMsgOutsCorrect pre post outs

  record Contract (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      inv           : RMPreservesInvariant pre post
      noEpochChange : NoEpochChange pre post
      outsCorrect   : OutsCorrect pre post outs

  -- TODO-2: Prove this
  postulate
    contract : ∀ pre → LBFT-weakestPre (handleProposal now pm) (Contract pre) pre

  contract! : ∀ pre → LBFT-Post-True (Contract pre) (handleProposal now pm) pre
  contract! pre = LBFT-contract (handleProposal now pm) (Contract pre) pre (contract pre)

  contract!-NoEpochChange : ∀ pre → LBFT-Post-True (λ r st outs → NoEpochChange pre st) (handleProposal now pm) pre
  contract!-NoEpochChange pre = Contract.noEpochChange (contract! pre)

  contract!-RMPreservesInvariant : ∀ pre → LBFT-Post-True (λ r st outs → RMPreservesInvariant pre st) (handleProposal now pm) pre
  contract!-RMPreservesInvariant pre = Contract.inv (contract! pre)
