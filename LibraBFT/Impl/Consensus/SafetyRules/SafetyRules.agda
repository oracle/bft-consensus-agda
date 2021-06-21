{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto                   as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRules where

open RWST-do

postulate
  obmCheckSigner : SafetyRules → Bool
  extensionCheckM : VoteProposal → LBFT (ErrLog ⊎ VoteData)
  constructLedgerInfoM : Block → HashValue → LBFT (ErrLog ⊎ LedgerInfo)
  verifyQcM : QuorumCert → LBFT (ErrLog ⊎ Unit)

------------------------------------------------------------------------------

signer : SafetyRules → ErrLog ⊎ ValidatorSigner
signer self = maybeS (self ^∙ srValidatorSigner) (inj₁ unit) inj₂

------------------------------------------------------------------------------

-- PREFERRED ROUND RULE (2nd VOTING RULE) : this avoids voting to commit a conflicting Block
verifyAndUpdatePreferredRoundM : QuorumCert → SafetyData → LBFT (ErrLog ⊎ SafetyData)
verifyAndUpdatePreferredRoundM quorumCert safetyData = do
  let preferredRound = safetyData ^∙ sdPreferredRound
      oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
      twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound
  -- LBFT-ALGO v3:p6: "... votes in round k only if the QC inside the k proposal
  -- is at least" PreferredRound."
  ifM oneChainRound <? preferredRound
    then bail unit -- error: incorrect preferred round, QC round does not match preferred round
    else do
      updated ← ifM‖ twoChainRound >? preferredRound ≔
                     pure (safetyData & sdPreferredRound ∙~ twoChainRound) -- log: info: updated preferred round
                   ‖ twoChainRound <? preferredRound ≔
                     pure safetyData                                       -- log: info: 2-chain round is lower than preferred round, but 1-chain is higher
                   ‖ otherwise≔
                     pure safetyData
      ok updated

------------------------------------------------------------------------------

verifyEpochM : Epoch → SafetyData → LBFT (ErrLog ⊎ Unit)
verifyEpochM epoch safetyData =
  ifM not ⌊ epoch ≟ℕ safetyData ^∙ sdEpoch ⌋
    then bail unit -- log: error: incorrect epoch
    else ok unit

------------------------------------------------------------------------------

-- INCREASING ROUND RULE (1st VOTING RULE) : ensures voting only ONCE per round
verifyAndUpdateLastVoteRoundM : Round → SafetyData → LBFT (ErrLog ⊎ SafetyData)
verifyAndUpdateLastVoteRoundM round safetyData =
  -- LBFT-ALGO v3:p6 : "... votes in round k it if is higher than" LastVotedRound
  ifM round >? (safetyData ^∙ sdLastVotedRound)
    then ok (safetyData & sdLastVotedRound ∙~ round )
    else bail unit -- log: error: incorrect last vote round

------------------------------------------------------------------------------

constructAndSignVoteM-continue0 : VoteProposal → ValidatorSigner → LBFT (ErrLog ⊎ Vote)
constructAndSignVoteM-continue1 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (ErrLog ⊎ Vote)
constructAndSignVoteM-continue2 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (ErrLog ⊎ Vote)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (ErrLog ⊎ Vote)
constructAndSignVoteM maybeSignedVoteProposal = do
  vs ← use (lSafetyRules ∙ srValidatorSigner)
  caseMM vs of λ where
    nothing → bail unit -- error: srValidatorSigner is nothing
    (just validatorSigner) → do
      let voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
      constructAndSignVoteM-continue0 voteProposal validatorSigner

module constructAndSignVoteM-continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where
  step₀ : LBFT (ErrLog ⊎ Vote)
  step₁ : SafetyData → LBFT (ErrLog ⊎ Vote)

  proposedBlock = voteProposal ^∙ vpBlock
  step₀ = do
    safetyData0 ← use (lPersistentSafetyStorage ∙ pssSafetyData)
    verifyEpochM (proposedBlock ^∙ bEpoch) safetyData0 ∙?∙ λ _ → step₁ safetyData0
  step₁ safetyData0 = do
      caseMM (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifM vote ^∙ vVoteData ∙ vdProposed ∙ biRound ≟ℕ (proposedBlock ^∙ bRound)
            then ok vote
            else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
        nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

constructAndSignVoteM-continue0 = constructAndSignVoteM-continue0.step₀

module constructAndSignVoteM-continue1
  (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner)
  (proposedBlock : Block)        (safetyData0     : SafetyData) where

  step₀ : LBFT (ErrLog ⊎ Vote)
  step₁ : LBFT (ErrLog ⊎ Vote)
  step₂ : ValidatorVerifier → LBFT (ErrLog ⊎ Vote)
  step₃ : LBFT (ErrLog ⊎ Vote)

  step₀ =
    verifyQcM (proposedBlock ^∙ bQuorumCert) ∙?∙ λ _ → step₁
  step₁ = do
      validatorVerifier ← gets rmGetValidatorVerifier
      step₂ validatorVerifier
  step₂ validatorVerifier =
      pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙ λ _ → step₃
  step₃ =
        verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
        constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock

constructAndSignVoteM-continue1 = constructAndSignVoteM-continue1.step₀

module constructAndSignVoteM-continue2 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner)
                                       (proposedBlock : Block) (safetyData : SafetyData) where
  step₀ : LBFT (ErrLog ⊎ Vote)
  step₁ : SafetyData → LBFT (ErrLog ⊎ Vote)
  step₂ : SafetyData → VoteData → LBFT (ErrLog ⊎ Vote)
  step₃ : SafetyData → VoteData → Author → LedgerInfo → LBFT (ErrLog ⊎ Vote)

  step₀ = verifyAndUpdateLastVoteRoundM (proposedBlock ^∙ bBlockData ∙ bdRound) safetyData ∙?∙ step₁

  step₁ safetyData1 = do
    lSafetyData ∙= safetyData1
    extensionCheckM voteProposal ∙?∙ (step₂ safetyData1)

  step₂ safetyData1 voteData = do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData) ∙?∙ (step₃ safetyData1 voteData author)

  step₃ safetyData1 voteData author ledgerInfo = do
        let signature = ValidatorSigner.sign ⦃ obm-dangerous-magic! ⦄ validatorSigner ledgerInfo
            vote      = Vote.newWithSignature voteData author ledgerInfo signature
        lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)
        ok vote

constructAndSignVoteM-continue2 = constructAndSignVoteM-continue2.step₀


