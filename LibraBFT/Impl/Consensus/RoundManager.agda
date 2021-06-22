{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore      as BlockStore
open import LibraBFT.Impl.Consensus.BlockStorage.SyncManager     as SyncManager
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection    as ProposerElection
open import LibraBFT.Impl.Consensus.Liveness.RoundState          as RoundState hiding (processCertificatesM)
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage    as PersistentLivenessStorage
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules      as SafetyRules
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId


module LibraBFT.Impl.Consensus.RoundManager where

open RWST-do

------------------------------------------------------------------------------

processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
processCommitM finalityProof = pure []

-- IMPL-TODO: implement this
processNewRoundEventM : Instant → NewRoundEvent → LBFT Unit
processNewRoundEventM now nre = pure unit

------------------------------------------------------------------------------

ensureRoundAndSyncUpM : Instant → Round    → SyncInfo → Author → Bool → LBFT (FakeErr ⊎ Bool)
processProposalM      : Block                                         → LBFT Unit
executeAndVoteM       : Block                                         → LBFT (FakeErr ⊎ Vote)

-- external entry point
-- TODO-2: The sync info that the peer requests if it discovers that its round
-- state is behind the sender's should be sent as an additional argument, for now.
module processProposalMsgM (now : Instant) (pm : ProposalMsg) where
  step₀ : LBFT Unit
  step₁ : Author → LBFT Unit
  step₂ : FakeErr ⊎ Bool → LBFT Unit

  step₀ =
    case pm ^∙ pmProposer of λ where
      nothing → logInfo -- log: info: proposal with no author
      (just pAuthor) → step₁ pAuthor
  step₁ pAuthor =
        ensureRoundAndSyncUpM now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo)
                              pAuthor true >>= step₂
  step₂ r =
        -- IMPL-DIFF: We use `ifM` to test whether the round of the proposal is
        -- current, to take advantage of the obligations `RWST-weakestPre` generates.
        case r of λ where
        (inj₁ _) → logErr -- log: error: <propagate error>
        (inj₂ pmCurrent) →
          if pmCurrent
            then processProposalM (pm ^∙ pmProposal)
            else do
              currentRound ← use (lRoundState ∙ rsCurrentRound)
              logInfo  -- log: info: dropping proposal for old round

processProposalMsgM = processProposalMsgM.step₀

------------------------------------------------------------------------------

-- TODO-2: Implement this.
postulate
  syncUpM : Instant → SyncInfo → Author → Bool → LBFT (FakeErr ⊎ Unit)

------------------------------------------------------------------------------

module ensureRoundAndSyncUpM
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo) (author : Author) (helpRemote : Bool) where
  step₀ : LBFT (FakeErr ⊎ Bool)
  step₁ : LBFT (FakeErr ⊎ Bool)
  step₂ : LBFT (FakeErr ⊎ Bool)

  step₀ = do
    currentRound ← use (lRoundState ∙ rsCurrentRound)
    if ⌊ messageRound <? currentRound ⌋
      then ok false
      else step₁
  step₁ =
        syncUpM now syncInfo author helpRemote ∙?∙ λ _ → step₂
  step₂ = do
          currentRound' ← use (lRoundState ∙ rsCurrentRound)
          if not ⌊ messageRound ≟ℕ currentRound' ⌋
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
module ProcessProposalM (proposal : Block) where
  step₀ : LBFT Unit
  step₁ : ∀ {pre} → BlockStore (α-EC-RM pre) → Bool → LBFT Unit
  step₂ : FakeErr ⊎ Vote → LBFT Unit
  step₃ : Vote → LBFT Unit
  step₄ : Vote → SyncInfo → LBFT Unit

  step₀ = do
  -- DIFF: We cannot define a lens for the block store without dependent lenses,
  -- so here we first get the state.
    s ← get
    let bs = rmGetBlockStore s
    vp ← ProposerElection.isValidProposalM proposal
    step₁{s} bs vp
  step₁ bs vp =
    grd‖ is-nothing (proposal ^∙ bAuthor) ≔
         logErr -- log: error: proposal does not have an author
       ‖ not vp ≔
         logErr -- log: error: proposer for block is not valid for this round
       ‖ is-nothing (BlockStore.getQuorumCertForBlock (proposal ^∙ bParentId) bs) ≔
         logErr -- log: error: QC of parent is not in BS
       ‖ not (maybeS (BlockStore.getBlock (proposal ^∙ bParentId) bs) false
              λ parentBlock →
                ⌊ parentBlock ^∙ ebRound <?ℕ proposal ^∙ bRound ⌋) ≔
         logErr -- log: error: parentBlock < proposalRound
       ‖ otherwise≔ do
         -- DIFF: For the verification effort, we use special-purpose case
         -- distinction operators, so the Haskell
         -- > executeAndVoteM proposal >>= \case
         -- is translated to the following.
         r ← executeAndVoteM proposal
         step₂ r
  step₂ r =
         case r of λ where
           (inj₁ _) → logErr -- <propagate error>
           (inj₂ vote) → step₃ vote
  step₃ vote = do
             RoundState.recordVote vote
             si ← BlockStore.syncInfoM
             step₄ vote si
  step₄ vote si = do
             recipient ← ProposerElection.getValidProposer
                         <$> use lProposerElection
                         <*> pure (proposal ^∙ bRound + 1)
             act (SendVote (VoteMsg∙new vote si) (recipient ∷ []))
             -- TODO-2:                                                mkNodesInOrder1 recipient

processProposalM = ProcessProposalM.step₀

------------------------------------------------------------------------------
module ExecuteAndVoteM (b : Block) where
  step₀ :                 LBFT (FakeErr ⊎ Vote)
  step₁ : ExecutedBlock → LBFT (FakeErr ⊎ Vote)
  step₂ : ExecutedBlock → LBFT (FakeErr ⊎ Vote)
  step₃ : Vote  → LBFT (FakeErr ⊎ Vote)

  step₀ = BlockStore.executeAndInsertBlockM b ∙?∙ step₁
  step₁ eb = do
    cr ← use (lRoundState ∙ rsCurrentRound)
    vs ← use (lRoundState ∙ rsVoteSent)
    so ← use lSyncOnly
    grd‖ is-just vs
         ≔ bail fakeErr -- error: already voted this round
       ‖ so
         ≔ bail fakeErr -- error: sync-only set
       ‖ otherwise≔ step₂ eb
  step₂ eb = do
           let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
           SafetyRules.constructAndSignVoteM maybeSignedVoteProposal' {- ∙^∙ logging -}
             ∙?∙ step₃
  step₃ vote =   PersistentLivenessStorage.saveVoteM vote
             ∙?∙ λ _ → ok vote

executeAndVoteM = ExecuteAndVoteM.step₀

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
  if not (Vote.isTimeout vote)
  then (do
    let nextRound = vote ^∙ vVoteData ∙ vdProposed ∙ biRound + 1
    -- IMPL-TODO pgAuthor
    -- v ← ProposerElection.isValidProposer <$> (use lProposerElection
    --                                      <*> use (lRoundManager.pgAuthor) <*> pure nextRound)
    let v = true
    if v then continue else logErr)
  else
    continue
 where
  continue : LBFT Unit
  continue = do
    let blockId = vote ^∙ vVoteData ∙ vdProposed ∙ biId
    s ← get
    let bs = _epBlockStore (_rmWithEC s)
    if true -- (is-just (BlockStore.getQuorumCertForBlock blockId {!!})) -- IMPL-TODO
      then logInfo
      else addVoteM now vote -- TODO-1: logging

addVoteM now vote = do
  s ← get
  let bs = _epBlockStore (_rmWithEC s)
  {- IMPL-TODO make this commented code work then remove the 'continue' after the comment
  maybeS nothing (bs ^∙ bsHighestTimeoutCert) continue λ tc →
    if-dec vote ^∙ vRound =? tc ^∙ tcRound
    then logInfo
    else continue
  -}
  continue
 where
  continue : LBFT Unit
  continue = do
    rm ← get
    let verifier = _esVerifier (_rmEpochState (_rmEC rm))
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
    (inj₁ e)    → logErr -- TODO : Haskell logs err and returns ().  Do we need to return error?
    (inj₂ unit) → processCertificatesM now

newTcAggregatedM now tc =
  BlockStore.insertTimeoutCertificateM tc >>= λ where
    (inj₁ e)    → logErr -- TODO : Haskell logs err and returns ().  Do we need to return error?
    (inj₂ unit) → processCertificatesM now
