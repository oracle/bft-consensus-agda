{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRules where

open RWST-do

postulate
  obmCheckSigner sr : SafetyRules → Bool
  verifyEpochM : Epoch → SafetyData → LBFT (ErrLog ⊎ Unit)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (ErrLog ⊎ Vote)
constructAndSignVoteM maybeSignedVoteProposal = do
  sr ← use lSafetyRules
  if not (obmCheckSigner sr)
    then bail unit -- error: ["srValidatorSigner", "Noathing"]
    else do
      let voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
          _executionSignature = maybeSignedVoteProposal ^∙ msvpSignature
      use (lSafetyRules ∙ srExecutionPublicKey) >>= λ where
        (just _) → bail unit -- errorExitNow: verify execution signature not implemented
        nothing → continue0 voteProposal
  where
  continue1 : VoteProposal → Block → SafetyData → LBFT (ErrLog ⊎ Vote)

  continue0 : VoteProposal → LBFT (ErrLog ⊎ Vote)
  continue0 voteProposal = do
    let proposedBlock = voteProposal ^∙ vpBlock
    safetyData0 ← use (lPersistentSafetyStorage ∙ pssSafetyData)
    verifyEpochM (proposedBlock ^∙ bEpoch) safetyData0 ∙?∙ λ _ →
      case safetyData0 ^∙ sdLastVote of λ where
        (just vote) →
          grd‖ (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound)
               ≔ ok vote
             ‖ otherwise≔ continue1 voteProposal proposedBlock safetyData0
        nothing → continue1 voteProposal proposedBlock safetyData0


  -- TODO-1: Implement
  continue1 voteProposal proposedBlock safetyData0 = bail unit

