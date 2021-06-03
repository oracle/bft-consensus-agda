{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.Vote where

timeout : Vote → Timeout
timeout v =
  Timeout∙new (v ^∙ vVoteData ∙ vdProposed ∙ biEpoch) (v ^∙ vVoteData ∙ vdProposed ∙ biRound)

isTimeout : Vote → Bool
isTimeout v
    with v ^∙ vTimeoutSignature
... | (just _) = true
... | nothing  = false



