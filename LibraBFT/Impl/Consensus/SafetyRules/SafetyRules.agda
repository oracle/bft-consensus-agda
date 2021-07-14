{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData   as VoteData
import      LibraBFT.Impl.OBM.Crypto                          as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Types.BlockInfo                     as BlockInfo
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto                   as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRules where

------------------------------------------------------------------------------

signer : SafetyRules → Either ErrLog ValidatorSigner
signer self = maybeS (self ^∙ srValidatorSigner) (Left fakeErr {- error: signer not initialized -}) Right

------------------------------------------------------------------------------

extensionCheckM : VoteProposal → LBFT (Either ErrLog VoteData)
extensionCheckM voteProposal = do
  let proposedBlock = voteProposal ^∙ vpBlock
      obmAEP        = voteProposal ^∙ vpAccumulatorExtensionProof
  -- IMPL-TODO: verify .accumulator_extension_proof().verify ...
  ok (VoteData.new
       (Block.genBlockInfo
         proposedBlock
         -- OBM-LBFT-DIFF: completely different
         (Crypto.obmHashVersion (obmAEP ^∙ aepObmNumLeaves))
         (obmAEP ^∙ aepObmNumLeaves)
         (voteProposal ^∙ vpNextEpochState))
       (proposedBlock ^∙ bQuorumCert ∙ qcCertifiedBlock))

------------------------------------------------------------------------------

constructLedgerInfoM : Block → HashValue → LBFT (Either ErrLog LedgerInfo)
constructLedgerInfoM proposedBlock consensusDataHash = do
  let block2 = proposedBlock ^∙ bRound
      block1 = proposedBlock ^∙ bQuorumCert ∙ qcCertifiedBlock ∙ biRound
      block0 = proposedBlock ^∙ bQuorumCert ∙ qcParentBlock ∙ biRound
      commit = (block0 + 1 == block1) ∧ (block1 + 1 == block2)
  commitInfo ←
    if commit
    then (do
      let c = proposedBlock ^∙ bQuorumCert ∙ qcParentBlock
      logInfo fakeInfo -- lSR (Info3ChainDetected proposedBlock c)
      pure c)
    else
      pure BlockInfo.empty
  ok (LedgerInfo∙new commitInfo consensusDataHash)

------------------------------------------------------------------------------

-- PREFERRED ROUND RULE (2nd VOTING RULE) : this avoids voting to commit a conflicting Block
verifyAndUpdatePreferredRoundM : QuorumCert → SafetyData → LBFT (Either ErrLog SafetyData)
verifyAndUpdatePreferredRoundM quorumCert safetyData = do
  let preferredRound = safetyData ^∙ sdPreferredRound
      oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
      twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound
  -- LBFT-ALGO v3:p6: "... votes in round k only if the QC inside the k proposal
  -- is at least" PreferredRound."
  ifM oneChainRound <? preferredRound
    then bail fakeErr -- error: incorrect preferred round, QC round does not match preferred round
    else do
      updated ← ifM‖ twoChainRound >? preferredRound ≔ (do
                     logInfo fakeInfo  -- updated preferred round
                     pure (safetyData & sdPreferredRound ∙~ twoChainRound))
                   ‖ twoChainRound <? preferredRound ≔ (do
                     logInfo fakeInfo -- 2-chain round is lower than preferred round, but 1-chain is higher
                     pure safetyData)
                   ‖ otherwise≔
                     pure safetyData
      ok updated

------------------------------------------------------------------------------

verifyEpochM : Epoch → SafetyData → LBFT (Either ErrLog Unit)
verifyEpochM epoch safetyData =
  ifM epoch /= safetyData ^∙ sdEpoch
    then bail fakeErr -- incorrect epoch
    else ok unit

------------------------------------------------------------------------------

-- INCREASING ROUND RULE (1st VOTING RULE) : ensures voting only ONCE per round
verifyAndUpdateLastVoteRoundM : Round → SafetyData → LBFT (Either ErrLog SafetyData)
verifyAndUpdateLastVoteRoundM round safetyData =
  -- LBFT-ALGO v3:p6 : "... votes in round k it if is higher than" LastVotedRound
  ifM round >? (safetyData ^∙ sdLastVotedRound)
    then ok (safetyData & sdLastVotedRound ∙~ round )
    else bail fakeErr -- incorrect last vote round

------------------------------------------------------------------------------

verifyQcM : QuorumCert → LBFT (Either ErrLog Unit)
verifyQcM qc = do
  validatorVerifier ← use (lRoundManager ∙ srValidatorVerifier)
  pure (QuorumCert.verify qc validatorVerifier) ∙^∙ withErrCtx ("InvalidQuorumCertificate" ∷ [])

------------------------------------------------------------------------------

constructAndSignVoteM-continue0 : VoteProposal → ValidatorSigner                       → LBFT (Either ErrLog Vote)
constructAndSignVoteM-continue1 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (Either ErrLog Vote)
constructAndSignVoteM-continue2 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (Either ErrLog Vote)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (Either ErrLog Vote)
constructAndSignVoteM maybeSignedVoteProposal =
  logEE ("" ∷ []) $ do
  vs ← use (lSafetyRules ∙ srValidatorSigner)
  maybeS vs (bail fakeErr {- srValidatorSigner is nothing -}) λ validatorSigner → do
    let voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
    constructAndSignVoteM-continue0 voteProposal validatorSigner

module constructAndSignVoteM-continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where
  step₀ : LBFT (Either ErrLog Vote)
  step₁ : SafetyData → LBFT (Either ErrLog Vote)

  proposedBlock = voteProposal ^∙ vpBlock

  step₀ = do
    safetyData0 ← use (lPersistentSafetyStorage ∙ pssSafetyData)
    verifyEpochM (proposedBlock ^∙ bEpoch) safetyData0 ∙?∙ λ _ → step₁ safetyData0

  step₁ safetyData0 = do
      caseMM (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifM vote ^∙ vVoteData ∙ vdProposed ∙ biRound == proposedBlock ^∙ bRound
            then ok vote
            else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
        nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

constructAndSignVoteM-continue0 = constructAndSignVoteM-continue0.step₀

module constructAndSignVoteM-continue1
  (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner)
  (proposedBlock : Block)        (safetyData0     : SafetyData) where

  step₀ : LBFT (Either ErrLog Vote)
  step₁ : LBFT (Either ErrLog Vote)
  step₂ : ValidatorVerifier → LBFT (Either ErrLog Vote)
  step₃ : LBFT (Either ErrLog Vote)

  step₀ =
    verifyQcM (proposedBlock ^∙ bQuorumCert) ∙?∙ λ _ → step₁

  step₁ = do
      validatorVerifier ← use (lRoundManager ∙ srValidatorVerifier)
      step₂ validatorVerifier

  step₂ validatorVerifier =
      pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙ λ _ → step₃

  step₃ =
        verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
        constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock

constructAndSignVoteM-continue1 = constructAndSignVoteM-continue1.step₀

module constructAndSignVoteM-continue2 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner)
                                       (proposedBlock : Block) (safetyData : SafetyData) where
  step₀ : LBFT (Either ErrLog Vote)
  step₁ : SafetyData → LBFT (Either ErrLog Vote)
  step₂ : SafetyData → VoteData → LBFT (Either ErrLog Vote)
  step₃ : SafetyData → VoteData → Author → LedgerInfo → LBFT (Either ErrLog Vote)

  step₀ =
    verifyAndUpdateLastVoteRoundM (proposedBlock ^∙ bBlockData ∙ bdRound) safetyData ∙?∙ step₁

  step₁ safetyData1 = do
    lSafetyData ∙= safetyData1  -- TODO-1: resolve discussion about pssSafetyData vs lSafetyData
    extensionCheckM voteProposal ∙?∙ (step₂ safetyData1)

  step₂ safetyData1 voteData = do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData)
                           ∙^∙ withErrCtx ("" ∷ []) ∙?∙ (step₃ safetyData1 voteData author)

  step₃ safetyData1 voteData author ledgerInfo = do
        let signature = ValidatorSigner.sign validatorSigner ledgerInfo
            vote      = Vote.newWithSignature voteData author ledgerInfo signature
        lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)
        logInfo fakeInfo -- InfoUpdateLastVotedRound
        ok vote

constructAndSignVoteM-continue2 = constructAndSignVoteM-continue2.step₀
