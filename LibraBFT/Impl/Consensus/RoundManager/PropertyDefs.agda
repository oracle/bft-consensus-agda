{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions of properties of only the behavior of the
-- handlers, nothing concerning the system state.

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.RoundManager.PropertyDefs where

NoOutputs : List Output → Set
NoOutputs outs = outs ≡ []

NoMsgOuts : List Output → Set
NoMsgOuts outs = List-filter isOutputMsg? outs ≡ []

++-NoMsgOuts : ∀ xs ys → NoMsgOuts xs → NoMsgOuts ys → NoMsgOuts (xs ++ ys)
++-NoMsgOuts xs ys nmo₁ nmo₂ = filter-++-[] xs ys isOutputMsg? nmo₁ nmo₂

VoteMsgOuts : List Output → VoteMsg → List Author → Set
VoteMsgOuts outs vm pids = List-filter isOutputMsg? outs ≡ (SendVote vm pids ∷ [])

++-NoMsgOuts-VoteMsgOuts : ∀ xs ys vm pids → NoMsgOuts xs → VoteMsgOuts ys vm pids → VoteMsgOuts (xs ++ ys) vm pids
++-NoMsgOuts-VoteMsgOuts xs ys vm pids nmo vmo
  rewrite List-filter-++ isOutputMsg? xs ys
  |       nmo
  |       vmo = refl

record NoEpochChange (pre post : RoundManager) : Set where
  constructor mkNoEpochChange
  field
    es≡₁ : (_rmEC pre) ≡L (_rmEC post) at rmEpoch
    es≡₂ : pre ≡L post at lSafetyData ∙ sdEpoch

reflNoEpochChange : ∀ {pre} → NoEpochChange pre pre
reflNoEpochChange = mkNoEpochChange refl refl

transNoEpochChange : ∀ {s₁ s₂ s₃} → NoEpochChange s₁ s₂ → NoEpochChange s₂ s₃ → NoEpochChange s₁ s₃
transNoEpochChange (mkNoEpochChange es≡₁ es≡₂) (mkNoEpochChange es≡₃ es≡₄) =
  mkNoEpochChange (trans es≡₁ es≡₃) (trans es≡₂ es≡₄)

-- For `processProposalMsg`, an emitted vote should satisfy the following
-- properties in relation to the pre/poststate and the epoch and round of the
-- proposal message.

record VoteCorrectInv (post : RoundManager) (round : Round) (vote : Vote) : Set where
  constructor mkVoteCorrectInv
  field
    round≡  : vote ^∙ vRound ≡ round
    postLv≡ : just vote ≡ post ^∙ lSafetyData ∙ sdLastVote

record VoteCorrectOld (pre post : RoundManager) (vote : Vote) : Set where
  constructor mkVoteCorrectOld
  field
    -- The implementation maintains an invariant that epoch of the vote stored in
    -- `sdLastVote` is the same as the peer's epoch.
    lvr≡ : pre ≡L post at lSafetyData ∙ sdLastVotedRound
    lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote

transVoteCorrectOld
  : ∀ {s₁ s₂ s₃ v}
    → VoteCorrectOld s₁ s₂ v → VoteCorrectOld s₂ s₃ v
    → VoteCorrectOld s₁ s₃ v
transVoteCorrectOld (mkVoteCorrectOld lvr≡ lv≡) (mkVoteCorrectOld lvr≡₁ lv≡₁) =
  mkVoteCorrectOld (trans lvr≡ lvr≡₁) (trans lv≡ lv≡₁)

record VoteCorrectNew (pre post : RoundManager) (epoch : Epoch) (vote : Vote) : Set where
  constructor mkVoteCorrectNew
  field
    epoch≡   : vote ^∙ vEpoch ≡ epoch
    lvr<     : pre [ _<_ ]L post at lSafetyData ∙ sdLastVotedRound
    postLvr≡ : vote ^∙ vRound ≡ post ^∙ lSafetyData ∙ sdLastVotedRound

record VoteCorrect (pre post : RoundManager) (epoch : Epoch) (round : Round) (vote : Vote) : Set where
  constructor mkVoteCorrect
  field
    inv     : VoteCorrectInv post round vote
    voteSrc : VoteCorrectOld pre post vote
              ⊎ VoteCorrectNew pre post epoch vote

VoteNotSaved : (pre post : RoundManager) (epoch : Epoch) (round : Round) → Set
VoteNotSaved pre post epoch round = ∃[ v ] VoteCorrect pre post epoch round v

record NoVoteCorrect (pre post : RoundManager) : Set where
  constructor mkNoVoteCorrect
  field
    lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote
    lvr≤ : pre [ _≤_ ]L post at lSafetyData ∙ sdLastVotedRound

reflNoVoteCorrect : ∀ {pre} → NoVoteCorrect pre pre
reflNoVoteCorrect = mkNoVoteCorrect refl ≤-refl

transNoVoteCorrect : ∀ {s₁ s₂ s₃} → NoVoteCorrect s₁ s₂ → NoVoteCorrect s₂ s₃ → NoVoteCorrect s₁ s₃
transNoVoteCorrect (mkNoVoteCorrect lv≡ lvr≤) (mkNoVoteCorrect lv≡₁ lvr≤₁) =
  mkNoVoteCorrect (trans lv≡ lv≡₁) (≤-trans lvr≤ lvr≤₁)

substVoteCorrect
  : ∀ {pre₁ pre₂ post₁ post₂ e₁ e₂ r₁ r₂ v}
    → pre₁  ≡L pre₂  at (lSafetyData ∙ sdLastVote)
    → pre₁  ≡L pre₂  at (lSafetyData ∙ sdLastVotedRound)
    → post₁ ≡L post₂ at (lSafetyData ∙ sdLastVote)
    → post₁ ≡L post₂ at (lSafetyData ∙ sdLastVotedRound)
    → e₁ ≡ e₂ → r₁ ≡ r₂
    → VoteCorrect pre₁ post₁ e₁ r₁ v
    → VoteCorrect pre₂ post₂ e₂ r₂ v
substVoteCorrect refl refl refl refl refl refl (mkVoteCorrect (mkVoteCorrectInv round≡ postLv≡) (Left (mkVoteCorrectOld lvr≡ lv≡))) =
  mkVoteCorrect (mkVoteCorrectInv round≡ postLv≡) (Left (mkVoteCorrectOld lvr≡ lv≡))
substVoteCorrect refl refl refl refl refl refl (mkVoteCorrect (mkVoteCorrectInv round≡ postLv≡) (Right (mkVoteCorrectNew epoch≡ lvr< postLvr≡))) =
  mkVoteCorrect (mkVoteCorrectInv round≡ postLv≡) (Right (mkVoteCorrectNew epoch≡ lvr< postLvr≡))
