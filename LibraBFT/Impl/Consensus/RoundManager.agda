{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

------------------------------------------------------------------------------
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap                                  as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore      as BlockStore
open import LibraBFT.Impl.Consensus.BlockStorage.SyncManager     as SyncManager
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection    as ProposerElection
import      LibraBFT.Impl.Consensus.Liveness.ProposalGenerator   as ProposalGenerator
open import LibraBFT.Impl.Consensus.Liveness.RoundState          as RoundState hiding (processCertificatesM)
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage    as PersistentLivenessStorage
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules      as SafetyRules
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
-----------------------------------------------------------------------------
import      Data.String                                          as String
------------------------------------------------------------------------------

module LibraBFT.Impl.Consensus.RoundManager where

------------------------------------------------------------------------------

processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
processCommitM finalityProof = pure []

------------------------------------------------------------------------------

generateProposalM
  : Instant → NewRoundEvent
  → LBFT (Either ErrLog ProposalMsg)

processNewRoundEventM : Instant → NewRoundEvent → LBFT Unit
processNewRoundEventM now nre = do
  logInfo fakeInfo   -- (InfoNewRoundEvent nre)
  gets rmPgAuthor >>= λ where
    nothing       → logErr fakeErr -- (here ["lRoundManager.pgAuthor", "Nothing"])
    (just author) → do
      v ← ProposerElection.isValidProposer <$> use lProposerElection <*> pure author <*> pure (nre ^∙ nreRound)
      when v $ do
        rcvrs ← gets rmObmAllAuthors -- use (lRoundManager.rmObmAllAuthors)
        generateProposalM now nre >>= λ where
          -- (Left (ErrEpochEndedNoProposals t)) -> logInfoL (lEC.|.lPM) (here ("EpochEnded":t))
          (Left e)            → logErr (withErrCtx (here' ("Error generating proposal" ∷ [])) e)
          (Right proposalMsg) → act (BroadcastProposal proposalMsg rcvrs)
 where
  here' : List String.String → List String.String
  here' t = "RoundManager" ∷ "processNewRoundEventM" ∷ t

generateProposalM now newRoundEvent =
  ProposalGenerator.generateProposalM now (newRoundEvent ^∙ nreRound) ∙?∙ λ proposal →
  SafetyRules.signProposalM proposal ∙?∙ λ signedProposal →
  Right ∘ ProposalMsg∙new signedProposal <$> BlockStore.syncInfoM

------------------------------------------------------------------------------

ensureRoundAndSyncUpM : Instant → Round    → SyncInfo → Author → Bool → LBFT (Either ErrLog Bool)
processProposalM      : Block                                         → LBFT Unit
executeAndVoteM       : Block                                         → LBFT (Either ErrLog Vote)

-- external entry point
-- TODO-2: The sync info that the peer requests if it discovers that its round
-- state is behind the sender's should be sent as an additional argument, for now.
module processProposalMsgM (now : Instant) (pm : ProposalMsg) where
  step₀ : LBFT Unit
  step₁ : Author → LBFT Unit
  step₂ : Either ErrLog Bool → LBFT Unit

  step₀ =
    caseMM pm ^∙ pmProposer of λ where
      nothing → logInfo fakeInfo -- proposal with no author
      (just pAuthor) → step₁ pAuthor

  step₁ pAuthor =
        ensureRoundAndSyncUpM now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo)
                              pAuthor true >>= step₂

  step₂ =
        λ where
          (Left e)      → logErr e
          (Right true)  → processProposalM (pm ^∙ pmProposal)
          (Right false) → do
            currentRound ← use (lRoundState ∙ rsCurrentRound)
            logInfo fakeInfo -- dropping proposal for old round

abstract
  processProposalMsgM = processProposalMsgM.step₀

  processProposalMsgM≡ : processProposalMsgM ≡ processProposalMsgM.step₀
  processProposalMsgM≡ = refl

------------------------------------------------------------------------------

-- TODO-2: Implement this.
postulate
  syncUpM : Instant → SyncInfo → Author → Bool → LBFT (Either ErrLog Unit)

------------------------------------------------------------------------------

module ensureRoundAndSyncUpM
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo) (author : Author) (helpRemote : Bool) where
  step₀ : LBFT (Either ErrLog Bool)
  step₁ : LBFT (Either ErrLog Bool)
  step₂ : LBFT (Either ErrLog Bool)

  step₀ = do
    currentRound ← use (lRoundState ∙ rsCurrentRound)
    ifM messageRound <? currentRound
      then ok false
      else step₁

  step₁ =
        syncUpM now syncInfo author helpRemote ∙?∙ λ _ → step₂

  step₂ = do
          currentRound' ← use (lRoundState ∙ rsCurrentRound)
          ifM messageRound /= currentRound'
            then bail fakeErr -- error: after sync, round does not match local
            else ok true

ensureRoundAndSyncUpM = ensureRoundAndSyncUpM.step₀

------------------------------------------------------------------------------

processCertificatesM : Instant → LBFT Unit
processCertificatesM now = do
  syncInfo ← BlockStore.syncInfoM
  maybeSMP (RoundState.processCertificatesM now syncInfo) unit (processNewRoundEventM now)

------------------------------------------------------------------------------

-- This function is broken into smaller pieces to aid in the verification
-- effort. The style of indentation used is to make side-by-side reading of the
-- Haskell prototype and Agda model easier.
module processProposalM (proposal : Block) where
  step₀ : LBFT Unit
  step₁ : BlockStore → (Either ObmNotValidProposerReason Unit) → LBFT Unit
  step₂ : Either ErrLog Vote → LBFT Unit
  step₃ : Vote → SyncInfo → LBFT Unit

  step₀ = do
    bs ← use lBlockStore
    vp ← ProposerElection.isValidProposalM proposal
    step₁ bs vp

  step₁ bs vp =
    ifM‖ isLeft vp ≔
         logErr fakeErr -- proposer for block is not valid for this round
       ‖ is-nothing (BlockStore.getQuorumCertForBlock (proposal ^∙ bParentId) bs) ≔
         logErr fakeErr -- QC of parent is not in BS
       ‖ not (maybeS (BlockStore.getBlock (proposal ^∙ bParentId) bs) false
              λ parentBlock →
                ⌊ parentBlock ^∙ ebRound <?ℕ proposal ^∙ bRound ⌋) ≔
         logErr fakeErr -- parentBlock < proposalRound
       ‖ otherwise≔ do
           executeAndVoteM proposal >>= step₂

  step₂ =  λ where
             (Left e)     → logErr e
             (Right vote) → do
               RoundState.recordVote vote
               si ← BlockStore.syncInfoM
               step₃ vote si

  step₃ vote si = do
               recipient ← ProposerElection.getValidProposer
                           <$> use lProposerElection
                           <*> pure (proposal ^∙ bRound + 1)
               act (SendVote (VoteMsg∙new vote si) (recipient ∷ []))
               -- TODO-2:                           mkNodesInOrder1 recipient

processProposalM = processProposalM.step₀

------------------------------------------------------------------------------
module executeAndVoteM (b : Block) where
  step₀ :                 LBFT (Either ErrLog Vote)
  step₁ : ExecutedBlock → LBFT (Either ErrLog Vote)
  step₂ : ExecutedBlock → LBFT (Either ErrLog Vote)
  step₃ : Vote          → LBFT (Either ErrLog Vote)

  step₀ =
    BlockStore.executeAndInsertBlockM b ∙^∙ withErrCtx ("" ∷ []) ∙?∙ step₁

  step₁ eb = do
    cr ← use (lRoundState ∙ rsCurrentRound)
    vs ← use (lRoundState ∙ rsVoteSent)
    so ← use lSyncOnly
    ifM‖ is-just vs ≔
         bail fakeErr -- error: already voted this round
       ‖ so ≔
         bail fakeErr -- error: sync-only set
       ‖ otherwise≔ step₂ eb

  step₂ eb = do
           let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
           SafetyRules.constructAndSignVoteM maybeSignedVoteProposal' {- ∙^∙ logging -}
             ∙?∙ step₃

  step₃ vote =   PersistentLivenessStorage.saveVoteM vote
             ∙?∙ λ _ → ok vote

executeAndVoteM = executeAndVoteM.step₀

------------------------------------------------------------------------------

processVoteM     : Instant → Vote                → LBFT Unit
addVoteM         : Instant → Vote                → LBFT Unit
newQcAggregatedM : Instant → QuorumCert → Author → LBFT Unit
newTcAggregatedM : Instant → TimeoutCertificate  → LBFT Unit

processVoteMsgM : Instant → VoteMsg → LBFT Unit
processVoteMsgM now voteMsg = do
  -- TODO ensureRoundAndSyncUp
  processVoteM now (voteMsg ^∙ vmVote)

processVoteM now vote =
  ifM not (Vote.isTimeout vote)
  then (do
    let nextRound = vote ^∙ vVoteData ∙ vdProposed ∙ biRound + 1
    gets rmPgAuthor >>= λ where
      nothing       → logErr fakeErr -- "lRoundManager.pgAuthor", "Nothing"
      (just author) → do
        v ← ProposerElection.isValidProposer <$> use lProposerElection
                                             <*> pure author <*> pure nextRound
        if v then continue else logErr fakeErr) -- "received vote, but I am not proposer for round"
  else
    continue
 where
  continue : LBFT Unit
  continue = do
    let blockId = vote ^∙ vVoteData ∙ vdProposed ∙ biId
    bs ← use lBlockStore
    ifM is-just (BlockStore.getQuorumCertForBlock blockId bs)
      then logInfo fakeInfo -- "block already has QC", "dropping unneeded vote"
      else do
      logInfo fakeInfo -- "before"
      addVoteM now vote
      pvA ← use lPendingVotes
      logInfo fakeInfo -- "after"

addVoteM now vote = do
  bs ← use lBlockStore
  maybeS-RWST (bs ^∙ bsHighestTimeoutCert) continue λ tc →
    ifM vote ^∙ vRound == tc ^∙ tcRound
      then logInfo fakeInfo -- "block already has TC", "dropping unneeded vote"
      else continue
 where
  continue : LBFT Unit
  continue = do
    verifier ← use (rmEpochState ∙ esVerifier)
    r ← RoundState.insertVoteM vote verifier
    case r of λ where
      (NewQuorumCertificate qc) →
        newQcAggregatedM now qc (vote ^∙ vAuthor)
      (NewTimeoutCertificate tc) →
        newTcAggregatedM now tc
      _ →
        pure unit

newQcAggregatedM now qc a =
  SyncManager.insertQuorumCertM qc (BlockRetriever∙new now a) >>= λ where
    (Left e)     → logErr e
    (Right unit) → processCertificatesM now

newTcAggregatedM now tc =
  BlockStore.insertTimeoutCertificateM tc >>= λ where
    (Left e)     → logErr e
    (Right unit) → processCertificatesM now
