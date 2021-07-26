{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.ConsensusTypes.ProposalMsg as ProposalMsg
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteMsg     as VoteMsg
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.Network where

processProposal : {- NodeId → -} ProposalMsg → Epoch → ValidatorVerifier → Either (Either ErrLog InfoLog) Unit
processProposal {- peerId -} proposal myEpoch vv =
  case pProposal of λ where
    (Left e) → Left (Left e)
    (Right unit) →
      grd‖ proposal ^∙ pmProposal ∙ bEpoch == myEpoch ≔
           pure unit
         -- TODO : push this onto a queue if epoch is in future (is this still relevant?)
         ‖ proposal ^∙ pmProposal ∙ bEpoch == myEpoch + 1 ≔
           Left (Right fakeInfo) -- proposal in new epoch arrived before my epoch change
         ‖ otherwise≔
           Left (Left fakeErr)   -- proposal for wrong epoch
  where
  pProposal = do
    ProposalMsg.verify proposal vv
    -- Note that our model does not assume knowledge of who sends a message, and therefore we do not
    -- check that the proposal is *sent* by the given peer (of course it must be *signed* by the
    -- peer, which is verified elsewhere).  Our proof should not require this.
    {- lcheck (proposal ^∙ pmProposal ∙ bAuthor == just peerId) -}

processVote : {- NodeId → -} VoteMsg → Epoch → ValidatorVerifier → Either (Either ErrLog InfoLog) Unit
processVote {- peerId -} voteMsg myEpoch vv =
  case pVote of λ where
    (Left e) → Left (Left e)
    (Right unit) →
      grd‖ voteMsg ^∙ vmEpoch == myEpoch ≔
        pure unit
         -- IMPL-TODO : push this onto a queue if epoch is in future (is this still relevant?)
         -- NOTE : epoch might be mismatched because
         -- - vote for EpochChange proposal round + 2 arrives
         --   after leader already already formed a quorum
         -- - timeout votes for previous or subsequent epochs arrive after the epoch change
         ‖ voteMsg ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch + 1 == myEpoch ≔
           Left (Right (fakeInfo {- (here $ "vote for previous epoch arrived after my epoch change" ∷ lsE myEpoch ∷ []) -}))
         ‖ voteMsg ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch == myEpoch + 1 ≔
           Left (Right (fakeInfo {- (here $ "vote for previous epoch arrived before my epoch change" ∷ lsE myEpoch ∷ []) -}))
         ‖ otherwise≔
           Left (Left (fakeErr {- (here $ "vote for wrong epoch" ∷ lsE myEpoch ∷ [])-}))
  where
 -- here t = "Network" ∷ "processVote" ∷ lsVM voteMsg ∷ t

  pVote : Either ErrLog Unit
  pVote = do
 -- See comment above about checking which peer *sent* the message.
 -- lcheck (voteMsg ^∙ vmVote ∙ vAuthor == peerId)
 --        (here $ "vote received must be from the sending peer" ∷ lsA peerId ∷ [])
    VoteMsg.verify voteMsg vv
