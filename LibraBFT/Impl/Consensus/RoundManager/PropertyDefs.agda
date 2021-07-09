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

NoVoteOuts : List Output → Set
NoVoteOuts outs = List-filter isSendVote? outs ≡ []

NoBroadcastOuts : List Output → Set
NoBroadcastOuts outs = List-filter isBroadcastProposal? outs ≡ []

NoMsgOuts : List Output → Set
NoMsgOuts outs = List-filter isOutputMsg? outs ≡ []

NoMsgOuts⇒NoVoteOuts : ∀ {outs} → NoMsgOuts outs → NoVoteOuts outs
NoMsgOuts⇒NoVoteOuts{outs} pf = filter-∪?-[]₂ outs isBroadcastProposal? isSendVote? pf

NoMsgOuts⇒NoBroadcastOuts : ∀ {outs} → NoMsgOuts outs → NoBroadcastOuts outs
NoMsgOuts⇒NoBroadcastOuts{outs} pf = filter-∪?-[]₁ outs isBroadcastProposal? isSendVote? pf

++-NoMsgOuts : ∀ xs ys → NoMsgOuts xs → NoMsgOuts ys → NoMsgOuts (xs ++ ys)
++-NoMsgOuts xs ys nmo₁ nmo₂ = filter-++-[] xs ys isOutputMsg? nmo₁ nmo₂

++-NoMsgOuts-NoVoteOuts : ∀ xs ys → NoMsgOuts xs → NoVoteOuts ys → NoVoteOuts (xs ++ ys)
++-NoMsgOuts-NoVoteOuts xs ys nmo nvo
  rewrite List-filter-++ isSendVote? xs ys
  |       filter-∪?-[]₂ xs isBroadcastProposal? isSendVote? nmo
  |       nvo = refl

++-NoVoteOuts : ∀ xs ys → NoVoteOuts xs → NoVoteOuts ys → NoVoteOuts (xs ++ ys)
++-NoVoteOuts xs ys nvo₁ nvo₂ = filter-++-[] xs ys isSendVote? nvo₁ nvo₂

++-NoMsgOuts-NoBroadcastOuts : ∀ xs ys → NoMsgOuts xs → NoBroadcastOuts ys → NoBroadcastOuts (xs ++ ys)
++-NoMsgOuts-NoBroadcastOuts xs ys nmo nbo
  rewrite List-filter-++ isBroadcastProposal? xs ys
  |       filter-∪?-[]₁ xs isBroadcastProposal? isSendVote? nmo
  |       nbo = refl

VoteMsgOuts : List Output → VoteMsg → List Author → Set
VoteMsgOuts outs vm pids = List-filter isSendVote? outs ≡ (SendVote vm pids ∷ [])

++-NoVoteOuts-VoteMsgOuts : ∀ xs ys vm pids → NoVoteOuts xs → VoteMsgOuts ys vm pids → VoteMsgOuts (xs ++ ys) vm pids
++-NoVoteOuts-VoteMsgOuts xs ys vm pids nvo vmo
  rewrite List-filter-++ isSendVote? xs ys
  |       nvo
  = vmo

++-NoMsgOuts-VoteMsgOuts : ∀ xs ys vm pids → NoMsgOuts xs → VoteMsgOuts ys vm pids → VoteMsgOuts (xs ++ ys) vm pids
++-NoMsgOuts-VoteMsgOuts xs ys vm pids nmo vmo =
  ++-NoVoteOuts-VoteMsgOuts xs ys vm pids (filter-∪?-[]₂ xs isBroadcastProposal? isSendVote? nmo) vmo

NoErrOuts : List Output → Set
NoErrOuts outs = List-filter isLogErr? outs ≡ []

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

reflVoteCorrectOld : ∀ {pre v} → VoteCorrectOld pre pre v
reflVoteCorrectOld = mkVoteCorrectOld refl refl

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

record NoVoteCorrect (pre post : RoundManager) (strict : Bool) : Set where
  constructor mkNoVoteCorrect
  field
    lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote
    lvr≡≤ : pre [ if strict then _≡_ else _≤_ ]L post at lSafetyData ∙ sdLastVotedRound

reflNoVoteCorrect : ∀ {pre strict} → NoVoteCorrect pre pre strict
reflNoVoteCorrect{strict = true} = mkNoVoteCorrect refl refl
reflNoVoteCorrect{strict = false} = mkNoVoteCorrect refl ≤-refl

transNoVoteCorrect : ∀ {s₁ s₂ s₃ strict₁ strict₂} → NoVoteCorrect s₁ s₂ strict₁ → NoVoteCorrect s₂ s₃ strict₂ → NoVoteCorrect s₁ s₃ (strict₁ ∧ strict₂)
transNoVoteCorrect {strict₁ = false} {false} (mkNoVoteCorrect lv≡ lvr≡≤) (mkNoVoteCorrect lv≡₁ lvr≡≤₁) =
  mkNoVoteCorrect (trans lv≡ lv≡₁) (≤-trans lvr≡≤ lvr≡≤₁)
transNoVoteCorrect {strict₁ = false} {true} (mkNoVoteCorrect lv≡ lvr≤) (mkNoVoteCorrect lv≡₁ lvr≡₁) =
  mkNoVoteCorrect (trans lv≡ lv≡₁) (≤-trans lvr≤ (≡⇒≤ lvr≡₁))
transNoVoteCorrect {strict₁ = true} {false} (mkNoVoteCorrect lv≡ lvr≡) (mkNoVoteCorrect lv≡₁ lvr≤₁) =
  mkNoVoteCorrect (trans lv≡ lv≡₁) (≤-trans (≡⇒≤ lvr≡) lvr≤₁)
transNoVoteCorrect {strict₁ = true} {true} (mkNoVoteCorrect lv≡ lvr≡) (mkNoVoteCorrect lv≡₁ lvr≡₁) =
  mkNoVoteCorrect (trans lv≡ lv≡₁) (trans lvr≡ lvr≡₁)

pseudotransVoteCorrect
  : ∀ {s₁ s₂ s₃ vote epoch round}
    → NoVoteCorrect s₁ s₂ true → VoteCorrect s₂ s₃ epoch round vote
    → VoteCorrect s₁ s₃ epoch round vote
pseudotransVoteCorrect (mkNoVoteCorrect lv≡ lvr≡≤) (mkVoteCorrect inv (Left (mkVoteCorrectOld lvr≡ lv≡₁))) =
  mkVoteCorrect inv (Left (mkVoteCorrectOld (trans lvr≡≤ lvr≡) (trans lv≡ lv≡₁)))
pseudotransVoteCorrect (mkNoVoteCorrect lv≡ lvr≡≤) (mkVoteCorrect inv (Right (mkVoteCorrectNew epoch≡ lvr< postLvr≡))) =
  mkVoteCorrect inv (Right (mkVoteCorrectNew epoch≡ (≤-trans (s≤s (≡⇒≤ lvr≡≤)) lvr<) postLvr≡))

pseudotransVoteNotSaved
  : ∀ {s₁ s₂ s₃ epoch round}
    → NoVoteCorrect s₁ s₂ true → VoteNotSaved s₂ s₃ epoch round
    → VoteNotSaved s₁ s₃ epoch round
pseudotransVoteNotSaved nvc (vote , vc) = vote , (pseudotransVoteCorrect nvc vc)

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

record VoteMsgOutsCorrect (pre post : RoundManager) (outs : List Output) (epoch : Epoch) (round : Round) : Set where
  constructor mkVoteMsgOutsCorrect
  field
    vm  : VoteMsg
    pid : Author
    voteMsgOuts : VoteMsgOuts outs vm (pid ∷ [])
    voteCorrect : VoteCorrect pre post epoch round (vm ^∙ vmVote)

record NoVoteMsgOutsCorrect (pre post : RoundManager) (outs : List Output) (strict : Bool) (epoch : Epoch) (round : Round) : Set where
  constructor mkNoVoteMsgOutsCorrect
  field
    noVoteOuts : NoVoteOuts outs
    nvc⊎vns    : NoVoteCorrect pre post strict ⊎ VoteNotSaved pre post epoch round

pseudotransNoVoteMsgOutsCorrect
  : ∀ {s₁ s₂ s₃ outs₁ outs₂ strict epoch round}
    → NoVoteOuts outs₁ → NoVoteCorrect s₁ s₂ true → NoVoteMsgOutsCorrect s₂ s₃ outs₂ strict epoch round
    → NoVoteMsgOutsCorrect s₁ s₃ (outs₁ ++ outs₂) strict epoch round
pseudotransNoVoteMsgOutsCorrect{outs₁ = outs₁}{outs₂}{strict} nvo nvc (mkNoVoteMsgOutsCorrect nvo' (Left nvc')) =
  mkNoVoteMsgOutsCorrect (++-NoVoteOuts outs₁ outs₂ nvo nvo')
    (Left (transNoVoteCorrect nvc nvc'))
pseudotransNoVoteMsgOutsCorrect{outs₁ = outs₁}{outs₂}{strict} nvo nvc (mkNoVoteMsgOutsCorrect nvo' (Right vns)) =
  mkNoVoteMsgOutsCorrect (++-NoVoteOuts outs₁ outs₂ nvo nvo') (Right (pseudotransVoteNotSaved nvc vns))

NoVote⊎VoteMsgOutsCorrect : (pre post : RoundManager) (outs : List Output) (epoch : Epoch) (round : Round) → Set
NoVote⊎VoteMsgOutsCorrect pre post outs epoch round =
  (Σ[ strict ∈ Bool ] NoVoteMsgOutsCorrect pre post outs strict epoch round)
  ⊎ VoteMsgOutsCorrect pre post outs epoch round
