{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS hiding (verify)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.Vote where

newWithSignature : VoteData → Author → LedgerInfo → Signature → Vote
newWithSignature voteData author ledgerInfo signature =
  Vote∙new voteData author ledgerInfo signature nothing

postulate
  verify : Vote → ValidatorVerifier → Either ErrLog Unit
  addTimeoutSignature : Vote → Signature → Vote

timeout : Vote → Timeout
timeout v =
  Timeout∙new (v ^∙ vVoteData ∙ vdProposed ∙ biEpoch) (v ^∙ vVoteData ∙ vdProposed ∙ biRound)

isTimeout : Vote → Bool
isTimeout v = is-just (v ^∙ vTimeoutSignature)



