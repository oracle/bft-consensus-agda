{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
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

-- signers
--------------------------------------------------
signer : SafetyRules → ErrLog ⊎ ValidatorSigner
signer self = maybeS (self ^∙ srValidatorSigner) (inj₁ unit) inj₂

-- verifyAndUpdatePreferredRoundM
--------------------------------------------------
-- PREFERRED ROUND RULE (2nd VOTING RULE) : this avoids voting to commit a conflicting Block
verifyAndUpdatePreferredRoundM : QuorumCert → SafetyData → LBFT (ErrLog ⊎ SafetyData)
verifyAndUpdatePreferredRoundM quorumCert safetyData = do
  let preferredRound = safetyData ^∙ sdPreferredRound
      oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
      twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound
  -- LBFT-ALGO v3:p6: "... votes in round k only if the QC inside the k proposal
  -- is at least" PreferredRound."
  if ⌊ oneChainRound <? preferredRound ⌋
    then bail unit -- error: incorrect preferred round, QC round does not match preferred round
    else do
      updated ← grd‖ twoChainRound >? preferredRound
                     ≔ pure (safetyData [ sdPreferredRound := twoChainRound ])
                     -- log: info: updated preferred round
                   ‖ twoChainRound <? preferredRound
                     ≔ pure safetyData
                     -- log: info: 2-chain round is lower than preferred round, but 1-chain is higher
                   ‖ otherwise≔
                     pure safetyData
      ok updated


-- verifyEpochM
--------------------------------------------------
verifyEpochM : Epoch → SafetyData → LBFT (ErrLog ⊎ Unit)
verifyEpochM epoch safetyData =
  if not ⌊ epoch ≟ℕ safetyData ^∙ sdEpoch ⌋
    then bail unit -- log: error: incorrect epoch
    else ok unit

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
constructAndSignVoteM-continue0 : VoteProposal → ValidatorSigner → LBFT (ErrLog ⊎ VoteWithMeta)
constructAndSignVoteM-continue1 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (ErrLog ⊎ VoteWithMeta)
constructAndSignVoteM-continue2 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (ErrLog ⊎ VoteWithMeta)
-- constructAndSignVoteM-continue2-c₃ : VoteProposal → Block → SafetyData → VoteData → LedgerInfo → LBFT (ErrLog ⊎ VoteWithMeta)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (ErrLog ⊎ VoteWithMeta)
constructAndSignVoteM maybeSignedVoteProposal = do
  vs ← use (lSafetyRules ∙ srValidatorSigner)
  case vs of λ where
    nothing → bail unit -- error: srValidatorSigner is nothing
    (just validatorSigner) → do
      let voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
      constructAndSignVoteM-continue0 voteProposal validatorSigner

constructAndSignVoteM-continue0 voteProposal validatorSigner = do
  let proposedBlock = voteProposal ^∙ vpBlock
  safetyData0 ← use (lPersistentSafetyStorage ∙ pssSafetyData)
  verifyEpochM (proposedBlock ^∙ bEpoch) safetyData0 ∙?∙ λ _ →
    case (safetyData0 ^∙ sdLastVote) of λ where
      (just vote) →
        if ⌊ (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound) ⌋
          then ok (VoteWithMeta∙new vote mvsLastVote)
          else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
      nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0 =
  verifyQcM (proposedBlock ^∙ bQuorumCert) ∙?∙ λ _ → do
    validatorVerifier ← gets rmGetValidatorVerifier
    pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙ λ _ →
      verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
      constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock

constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData =
  verifyAndUpdateLastVoteRoundM (proposedBlock ^∙ bBlockData ∙ bdRound) safetyData ∙?∙ λ safetyData1 → do
    lSafetyData ∙= safetyData1
    extensionCheckM voteProposal ∙?∙ λ voteData → do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData) ∙?∙ λ ledgerInfo → do
        let signature = ValidatorSigner.sign ⦃ obm-dangerous-magic! ⦄ validatorSigner ledgerInfo
            vote      = Vote.newWithSignature voteData author ledgerInfo signature
        lSafetyData ∙= (safetyData1 [ sdLastVote ?= vote ])
        ok (VoteWithMeta∙new vote mvsNew)
