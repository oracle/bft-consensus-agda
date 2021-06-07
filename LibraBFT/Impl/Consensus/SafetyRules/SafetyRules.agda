{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.Impl.Consensus.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Util.Crypto                         as Crypto
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRules where

open RWST-do

postulate
  obmCheckSigner : SafetyRules → Bool

  -- TODO-1: These two functions should require a proof that `signer` returns `inj₂`
  obmUnsafeSign : ∀ {C} ⦃ ws :  WithSig C ⦄ → SafetyRules → C → Signature
  obmUnsafeSigner : SafetyRules → ValidatorSigner

  extensionCheckM : VoteProposal → LBFT (ErrLog ⊎ VoteData)
  constructLedgerInfoM : Block → HashValue → LBFT (ErrLog ⊎ LedgerInfo)
  verifyQcM : QuorumCert → LBFT (ErrLog ⊎ Unit)
  verifyAndUpdatePreferredRoundM : QuorumCert → SafetyData → LBFT (ErrLog ⊎ SafetyData)
  verifyEpochM : Epoch → SafetyData → LBFT (ErrLog ⊎ Unit)

-- signers
--------------------------------------------------
signer : SafetyRules → ErrLog ⊎ ValidatorSigner
signer self = maybeS (self ^∙ srValidatorSigner) (inj₁ unit) inj₂

-- verifyAndUpdateLastVoteRoundM
--------------------------------------------------
-- INCREASING ROUND RULE (1st VOTING RULE) : ensures voting only ONCE per round
verifyAndUpdateLastVoteRoundM : Round → SafetyData → LBFT (ErrLog ⊎ SafetyData)
verifyAndUpdateLastVoteRoundM round safetyData =
  -- LBFT-ALGO v3:p6 : "... votes in round k it if is higher than" LastVotedRound
  if ⌊ round >? (safetyData ^∙ sdLastVotedRound) ⌋
    then ok (safetyData [ sdLastVotedRound := round ])
    else bail unit -- log: error: incorrect last vote round

-- constructAndSignVoteM
--------------------------------------------------
constructAndSignVoteM-continue0 : VoteProposal → LBFT (ErrLog ⊎ MetaVote)
constructAndSignVoteM-continue1 : VoteProposal → Block → SafetyData → LBFT (ErrLog ⊎ MetaVote)
constructAndSignVoteM-continue2 : VoteProposal → Block → SafetyData → LBFT (ErrLog ⊎ MetaVote)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (ErrLog ⊎ MetaVote)
constructAndSignVoteM maybeSignedVoteProposal = do
  sr ← use lSafetyRules
  if not (obmCheckSigner sr) -- TODO-1: The result of this check needs to be propagated.
    then bail unit -- error: ["srValidatorSigner", "Nothing"]
    else do
      let voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
          _executionSignature = maybeSignedVoteProposal ^∙ msvpSignature
      use (lSafetyRules ∙ srExecutionPublicKey) >>= λ where
        (just _) → bail unit -- errorExitNow: verify execution signature not implemented
        nothing → constructAndSignVoteM-continue0 voteProposal

constructAndSignVoteM-continue0 voteProposal = do
  let proposedBlock = voteProposal ^∙ vpBlock
  safetyData0 ← use (lPersistentSafetyStorage ∙ pssSafetyData)
  verifyEpochM (proposedBlock ^∙ bEpoch) safetyData0 ∙?∙ λ _ →
    case safetyData0 ^∙ sdLastVote of λ where
      (just vote) →
        grd‖ (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound)
             ≔ ok (MetaVote∙new vote mvsLastVote)
           ‖ otherwise≔ constructAndSignVoteM-continue1 voteProposal proposedBlock safetyData0
      nothing → constructAndSignVoteM-continue1 voteProposal proposedBlock safetyData0

constructAndSignVoteM-continue1 voteProposal proposedBlock safetyData0 =
  verifyQcM (proposedBlock ^∙ bQuorumCert) ∙?∙ λ _ → do
    _rm ← get
    let validatorVerifier = rmGetValidatorVerifier _rm
    pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙ λ _ →
      verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙ λ safetyData1 →
      constructAndSignVoteM-continue2 voteProposal proposedBlock safetyData1

constructAndSignVoteM-continue2 voteProposal proposedBlock safetyData =
  verifyAndUpdateLastVoteRoundM (proposedBlock ^∙ bBlockData ∙ bdRound) safetyData ∙?∙ λ safetyData1 → do
    lSafetyData ∙= safetyData1
    extensionCheckM voteProposal ∙?∙ λ voteData → do
      sr0 ← use lSafetyRules
      let author = obmUnsafeSigner sr0 ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData) ∙?∙ λ ledgerInfo → do
        sr1 ← use lSafetyRules
        let signature = obmUnsafeSign ⦃ obm-dangerous-magic! ⦄ sr1 ledgerInfo
            vote      = Vote.newWithSignature voteData author ledgerInfo signature
        lSafetyData ∙= (safetyData1 [ sdLastVote ?= vote ])
        ok (MetaVote∙new vote mvsNew)
