{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions of properties of only the behavior of the
-- handlers, nothing concerning the system state.

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util

module LibraBFT.Impl.Consensus.RoundManager.PropertyDefs where

NoOutputs : List Output → Set
NoOutputs outs = outs ≡ []

NoMsgOuts : List Output → Set
NoMsgOuts outs = List-filter isOutputMsg? outs ≡ []

record NoEpochChange (pre post : RoundManager) : Set where
  constructor mkNoEpochChange
  field
    es≡₁ : (_rmEC pre) ≡L (_rmEC post) at rmEpoch
    es≡₂ : pre ≡L post at lSafetyData ∙ sdEpoch

-- For `processProposalMsg`, an emitted vote should satisfy the following
-- properties in relation to the pre/poststate and the epoch and round of the
-- proposal message.

record VoteCorrectOld (pre post : RoundManager) (vote : Vote) : Set where
  constructor mkVoteCorrectOld
  field
    -- The implementation maintains an invariant that epoch of the vote stored in
    -- `sdLastVote` is the same as the peer's epoch.
    lvr≡ : pre ≡L post at lSafetyData ∙ sdLastVotedRound
    lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote

record VoteCorrectNew (pre post : RoundManager) (epoch : Epoch) (vote : Vote) : Set where
  constructor mkVoteCorrectNew
  field
    epoch≡   : vote ^∙ vEpoch ≡ epoch
    lvr<     : pre [ _<_ ]L post at lSafetyData ∙ sdLastVotedRound
    postLvr≡ : vote ^∙ vRound ≡ post ^∙ lSafetyData ∙ sdLastVotedRound

record VoteCorrect (pre post : RoundManager) (epoch : Epoch) (round : Round) (vote : Vote) : Set where
  constructor mkVoteCorrect
  field
    round≡  : vote ^∙ vRound ≡ round
    postLv≡ : just vote ≡ post ^∙ lSafetyData ∙ sdLastVote
    voteSrc : VoteCorrectOld pre post vote
              ⊎ VoteCorrectNew pre post epoch vote

record NoVoteCorrect (pre post : RoundManager) : Set where
  constructor mkNoVoteCorrect
  field
    lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote
    lvr≤ : pre [ _≤_ ]L post at lSafetyData ∙ sdLastVotedRound

substVoteCorrect
  : ∀ {pre₁ pre₂ post₁ post₂ e r v}
    → pre₁  ≡L pre₂  at (lSafetyData ∙ sdLastVote)
    → pre₁  ≡L pre₂  at (lSafetyData ∙ sdLastVotedRound)
    → post₁ ≡L post₂ at (lSafetyData ∙ sdLastVote)
    → post₁ ≡L post₂ at (lSafetyData ∙ sdLastVotedRound)
    → VoteCorrect pre₁ post₁ e r v
    → VoteCorrect pre₂ post₂ e r v
substVoteCorrect refl refl refl refl (mkVoteCorrect round≡ postLv≡ (Left (mkVoteCorrectOld lvr≡ lv≡))) =
  mkVoteCorrect round≡ postLv≡ (Left (mkVoteCorrectOld lvr≡ lv≡))
substVoteCorrect refl refl refl refl (mkVoteCorrect round≡ postLv≡ (Right (mkVoteCorrectNew epoch≡ lvr< postLvr≡))) =
  mkVoteCorrect round≡ postLv≡ (Right (mkVoteCorrectNew epoch≡ lvr< postLvr≡))
