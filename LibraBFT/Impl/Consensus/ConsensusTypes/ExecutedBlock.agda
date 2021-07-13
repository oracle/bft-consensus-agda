{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Execution.ExecutorTypes.StateComputeResult as StateComputeResult
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock where

maybeSignedVoteProposal : ExecutedBlock → MaybeSignedVoteProposal
maybeSignedVoteProposal self =
  MaybeSignedVoteProposal∙new
    (VoteProposal∙new (StateComputeResult.extensionProof (self ^∙ ebStateComputeResult))
                      (self ^∙ ebBlock)
                      (self ^∙ ebStateComputeResult ∙ scrEpochState))
