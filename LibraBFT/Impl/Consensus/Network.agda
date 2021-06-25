{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.ConsensusTypes.ProposalMsg as ProposalMsg
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.Network where

processProposal : {- NodeId → -} ProposalMsg → Epoch → ValidatorVerifier → (Either FakeErr FakeInfo) ⊎ Unit
processProposal {- peerId -} proposal myEpoch vv =
  case pProposal of λ where
    (Left e) → Left (Left e)
    (Right unit) →
      grd‖ proposal ^∙ pmProposal ∙ bEpoch == myEpoch ≔
           return unit
         -- TODO : push this onto a queue if epoch is in future (is this still relevant?)
         ‖ proposal ^∙ pmProposal ∙ bEpoch == myEpoch + 1 ≔
           Left (Right fakeInfo) -- proposal in new epoch arrived before my epoch change
         ‖ otherwise≔
           Left (Left fakeErr)   -- proposal for wrong epoch
  where
  pProposal = do
    ProposalMsg.verify proposal vv
    {- lcheck (proposal ^∙ pmProposal ∙ bAuthor == just peerId) -}
