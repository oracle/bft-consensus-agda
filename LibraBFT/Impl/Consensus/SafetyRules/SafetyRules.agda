{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

------------------------------------------------------------------------------
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block                as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert           as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote                 as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData             as VoteData
import      LibraBFT.Impl.Consensus.SafetyRules.PersistentSafetyStorage as PersistentSafetyStorage
import      LibraBFT.Impl.OBM.Crypto                                    as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.BlockInfo                               as BlockInfo
import      LibraBFT.Impl.Types.EpochChangeProof                        as EpochChangeProof
import      LibraBFT.Impl.Types.ValidatorSigner                         as ValidatorSigner
import      LibraBFT.Impl.Types.ValidatorVerifier                       as ValidatorVerifier
open import LibraBFT.Impl.Types.Verifier
import      LibraBFT.Impl.Types.Waypoint                                as Waypoint
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto                             as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                       as String
------------------------------------------------------------------------------

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRules where

------------------------------------------------------------------------------

new : PersistentSafetyStorage → Bool → Either ErrLog SafetyRules
new persistentStorage exportConsensusKey = do
  pure $ mkSafetyRules
    persistentStorage
    exportConsensusKey
    nothing
    nothing

------------------------------------------------------------------------------

signer : SafetyRules → Either ErrLog ValidatorSigner
signer self = maybeS (self ^∙ srValidatorSigner) (Left fakeErr {- error: signer not initialized -}) Right

------------------------------------------------------------------------------

extensionCheck : VoteProposal → Either ErrLog VoteData
extensionCheck voteProposal = do
  let proposedBlock = voteProposal ^∙ vpBlock
      obmAEP        = voteProposal ^∙ vpAccumulatorExtensionProof
  -- IMPL-TODO: verify .accumulator_extension_proof().verify ...
   in pure
     (VoteData.new
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
  ifD oneChainRound <? preferredRound
    then bail fakeErr -- error: incorrect preferred round, QC round does not match preferred round
    else do
      updated ← case (compare twoChainRound preferredRound) of λ where
          GT → do
            logInfo fakeInfo -- updated preferred round
            pure (safetyData & sdPreferredRound ∙~ twoChainRound)
          LT → do
            logInfo fakeInfo  -- 2-chain round is lower than preferred round, but 1-chain is higher
            pure safetyData
          EQ →
            pure safetyData
      ok updated

------------------------------------------------------------------------------

verifyAuthorM : Maybe Author → LBFT (Either ErrLog Unit)
verifyAuthorM author = do
  vs ← use (lSafetyRules ∙ srValidatorSigner)
  maybeS vs (bail fakeErr) {-(ErrL (here' ["srValidatorSigner", "Nothing"]))-} $ λ validatorSigner →
    maybeSD
      author
      (bail fakeErr) -- (ErrL (here' ["InvalidProposal", "No author found in the proposal"])))
      (\a ->
        ifD validatorSigner ^∙ vsAuthor /= a
        then bail fakeErr -- (ErrL (here' ["InvalidProposal", "Proposal author is not validator signer"]))
        else ok unit)
 where
  here' : List String.String → List String.String
  here' t = "SafetyRules" ∷ "verifyAuthorM" ∷ t

------------------------------------------------------------------------------

verifyEpochM : Epoch → SafetyData → LBFT (Either ErrLog Unit)
verifyEpochM epoch safetyData =
  ifD epoch /= safetyData ^∙ sdEpoch
    then bail fakeErr -- incorrect epoch
    else ok unit

------------------------------------------------------------------------------

-- INCREASING ROUND RULE (1st VOTING RULE) : ensures voting only ONCE per round
verifyAndUpdateLastVoteRoundM : Round → SafetyData → LBFT (Either ErrLog SafetyData)
verifyAndUpdateLastVoteRoundM round safetyData =
  -- LBFT-ALGO v3:p6 : "... votes in round k it if is higher than" LastVotedRound
  ifD round >? (safetyData ^∙ sdLastVotedRound)
    then ok (safetyData & sdLastVotedRound ∙~ round )
    else bail fakeErr -- incorrect last vote round

------------------------------------------------------------------------------

verifyQcM : QuorumCert → LBFT (Either ErrLog Unit)
verifyQcM qc = do
  validatorVerifier ← use (lRoundManager ∙ srValidatorVerifier)
  pure (QuorumCert.verify qc validatorVerifier) ∙^∙ withErrCtx ("InvalidQuorumCertificate" ∷ [])

------------------------------------------------------------------------------

consensusState : SafetyRules → ConsensusState
consensusState self =
  ConsensusState∙new (self ^∙ srPersistentStorage ∙ pssSafetyData)
                     (self ^∙ srPersistentStorage ∙ pssWaypoint)

------------------------------------------------------------------------------

-- ** NOTE: PAY PARTICULAR ATTENTION TO THIS FUNCTION **
-- ** Because : it is long with lots of branches, so easy to transcribe wrong. **
-- ** And if initialization is wrong, everything is wrong. **
initialize : SafetyRules → EpochChangeProof → Either ErrLog SafetyRules
initialize self proof = do
  let waypoint   = self ^∙ srPersistentStorage ∙ pssWaypoint
  lastLi         ← withErrCtx' (here' ("EpochChangeProof.verify" ∷ []))
                               (        EpochChangeProof.verify proof waypoint)
  let ledgerInfo = lastLi ^∙ liwsLedgerInfo
  epochState     ← maybeS (ledgerInfo ^∙ liNextEpochState)
                          (Left fakeErr) -- ["last ledger info has no epoch state"]
                          pure
  let currentEpoch = self ^∙ srPersistentStorage ∙ pssSafetyData ∙ sdEpoch
  if-dec currentEpoch <? epochState ^∙ esEpoch
    then (do
      waypoint'  ← withErrCtx' (here' ("Waypoint.newEpochBoundary" ∷ []))
                               (        Waypoint.newEpochBoundary ledgerInfo)
      continue1 (self & srPersistentStorage ∙ pssWaypoint    ∙~ waypoint'
                      & srPersistentStorage ∙ pssSafetyData  ∙~
                          SafetyData∙new (epochState ^∙ esEpoch) {-Round-} 0 {-Round-} 0 nothing)
                epochState)
    else continue1 self epochState
 where
  continue2 : SafetyRules → EpochState → Either ErrLog SafetyRules
  here'     : List String.String → List String.String

  continue1 : SafetyRules → EpochState → Either ErrLog SafetyRules
  continue1 self1 epochState =
    continue2 (self1 & srEpochState ?~ epochState) epochState

  continue2 self2 epochState = do
    let author = self2 ^∙ srPersistentStorage ∙ pssAuthor
    maybeS (ValidatorVerifier.getPublicKey (epochState ^∙ esVerifier) author)
      (Left fakeErr) -- ["ValidatorNotInSet", lsA author] $
      λ expectedKey → do
        let currKey = eitherS (signer self2)
                      (const nothing)
                      (just ∘ ValidatorSigner.publicKey_USE_ONLY_AT_INIT)
        grd‖ currKey == just expectedKey ≔
             Right self2

           ‖ self2 ^∙ srExportConsensusKey ≔ (do
              consensusKey ← withErrCtx' (here' ("ValidatorKeyNotFound" ∷ []))
                (PersistentSafetyStorage.consensusKeyForVersion
                  (self2 ^∙ srPersistentStorage) expectedKey)
              Right (self2 & srValidatorSigner ?~ ValidatorSigner∙new author consensusKey))

           ‖ otherwise≔
             Left fakeErr -- ["srExportConsensusKey", "False", "NOT IMPLEMENTED"]
  here' t = "SafetyRules" ∷ "initialize" ∷ t

------------------------------------------------------------------------------

constructAndSignVoteM-continue0 : VoteProposal → ValidatorSigner                       → LBFT (Either ErrLog Vote)
constructAndSignVoteM-continue1 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (Either ErrLog Vote)
constructAndSignVoteM-continue2 : VoteProposal → ValidatorSigner →  Block → SafetyData → LBFT (Either ErrLog Vote)

constructAndSignVoteM : MaybeSignedVoteProposal → LBFT (Either ErrLog Vote)
constructAndSignVoteM maybeSignedVoteProposal = do
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
      caseMD (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifD vote ^∙ vVoteData ∙ vdProposed ∙ biRound == proposedBlock ^∙ bRound
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
    pssSafetyData-rm ∙= safetyData1
    pure (extensionCheck voteProposal) ∙?∙ (step₂ safetyData1)

  step₂ safetyData1 voteData = do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData)
                           ∙^∙ withErrCtx ("" ∷ []) ∙?∙ (step₃ safetyData1 voteData author)

  step₃ safetyData1 voteData author ledgerInfo = do
        let signature = ValidatorSigner.sign validatorSigner ledgerInfo
            vote      = Vote.newWithSignature voteData author ledgerInfo signature
        pssSafetyData-rm ∙= (safetyData1 & sdLastVote ?~ vote)
        logInfo fakeInfo -- InfoUpdateLastVotedRound
        ok vote

constructAndSignVoteM-continue2 = constructAndSignVoteM-continue2.step₀

------------------------------------------------------------------------------

signProposalM : BlockData → LBFT (Either ErrLog Block)
signProposalM blockData = do
 vs ← use (lSafetyRules ∙ srValidatorSigner)
 maybeS vs (bail fakeErr) {-ErrL (here' ["srValidatorSigner", "Nothing"])-} $ λ validatorSigner → do
  safetyData ← use (lPersistentSafetyStorage ∙ pssSafetyData)
  verifyAuthorM (blockData ^∙ bdAuthor) ∙?∙ λ _ →
    verifyEpochM (blockData ^∙ bdEpoch) safetyData ∙?∙ λ _ →
      ifD blockData ^∙ bdRound ≤?ℕ safetyData ^∙ sdLastVotedRound
      then bail fakeErr
      -- {-     ErrL (here' [ "InvalidProposal"
      --                    , "Proposed round is not higher than last voted round "
      --                    , lsR (blockData ^∙ bdRound), lsR (safetyData ^∙ sdLastVotedRound) ])-}
      else do
        verifyQcM (blockData ^∙ bdQuorumCert) ∙?∙ λ _ →
          verifyAndUpdatePreferredRoundM (blockData ^∙ bdQuorumCert) safetyData ∙?∙ λ safetyData1 → do
            pssSafetyData-rm ∙= safetyData1
            let signature  = ValidatorSigner.sign validatorSigner blockData
            ok (Block.newProposalFromBlockDataAndSignature blockData signature)
 where
  here' : List String.String → List String.String
  here' t = "SafetyRules" ∷ "signProposalM" ∷ t

------------------------------------------------------------------------------

signTimeoutM : Timeout → LBFT (Either ErrLog Signature)
signTimeoutM timeout = do
 vs ← use (lSafetyRules ∙ srValidatorSigner)
 maybeS vs (bail fakeErr) {-"srValidatorSigner", "Nothing"-} $ λ validatorSigner → do
   safetyData ← use (lPersistentSafetyStorage ∙ pssSafetyData)
   verifyEpochM (timeout ^∙ toEpoch) safetyData ∙^∙ withErrCtx (here' []) ∙?∙ λ _ → do
     ifD‖ timeout ^∙ toRound ≤? safetyData ^∙ sdPreferredRound ≔
          bail fakeErr
          --(ErrIncorrectPreferredRound (here []) (timeout ^∙ toRound) (safetyData ^∙ sdPreferredRound))
        ‖ timeout ^∙ toRound <? safetyData ^∙ sdLastVotedRound ≔
          bail fakeErr
          --(ErrIncorrectLastVotedRound (here []) (timeout ^∙ toRound) (safetyData ^∙ sdLastVotedRound))
        ‖ timeout ^∙ toRound >? safetyData ^∙ sdLastVotedRound ≔
          verifyAndUpdateLastVoteRoundM (timeout ^∙ toRound) safetyData
            ∙^∙ withErrCtx (here' [])
            ∙?∙ (λ safetyData1 → do
            pssSafetyData-rm ∙= safetyData1
            logInfo fakeInfo -- (InfoUpdateLastVotedRound (timeout ^∙ toRound))
            continue validatorSigner)

        ‖ otherwise≔
          continue validatorSigner
 where
  continue : ValidatorSigner → LBFT (Either ErrLog Signature)
  continue validatorSigner = do
    let signature = ValidatorSigner.sign validatorSigner timeout
    ok signature

  here' : List String.String → List String.String
  here' t = "SafetyRules" ∷ "signTimeoutM" ∷ {-lsTO timeout ∷-}   t
