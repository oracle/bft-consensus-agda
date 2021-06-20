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

processNewRoundEventM : Instant → NewRoundEvent → LBFT Unit
processNewRoundEventM now nre = pure unit

------------------------------------------------------------------------------

syncUpM               : Instant → SyncInfo → Author                   → LBFT (ErrLog ⊎ Unit)
ensureRoundAndSyncUpM : Instant → Round    → SyncInfo → Author → Bool → LBFT (ErrLog ⊎ Bool)
processProposalM      : Block                                         → LBFT Unit
executeAndVoteM       : Block                                         → LBFT (ErrLog ⊎ VoteWithMeta)

-- external entry point
-- TODO-2: The sync info that the peer requests if it discovers that its round
-- state is behind the sender's should be sent as an additional argument, for now.
processProposalMsgM : Instant → {- Author → -} ProposalMsg → LBFT Unit
processProposalMsgM now {- from -} pm =
  case pm ^∙ pmProposer of λ where
    nothing        → pure unit -- log: info: proposal with no author
    (just pAuthor) →
      ensureRoundAndSyncUpM now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo)
                            pAuthor true >>= λ where
      (inj₁ _)     → pure unit -- log: error: <propagate error>
      (inj₂ true)  → processProposalM (pm ^∙ pmProposal)
      (inj₂ false) → do
        currentRound ← use (lRoundState ∙ rsCurrentRound)
        pure unit -- log: info: dropping proposal for old round

------------------------------------------------------------------------------

-- TODO-2: Implement this.
syncUpM now syncInfo author = ok unit

------------------------------------------------------------------------------

ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote = do
  currentRound ← use (lRoundState ∙ rsCurrentRound)
  if ⌊ messageRound <? currentRound ⌋
     then ok false
     else syncUpM now syncInfo author ∙?∙ λ _ → do
       currentRound' ← use (lRoundState ∙ rsCurrentRound)
       if not ⌊ messageRound ≟ℕ currentRound' ⌋
         then bail unit  -- error: after sync, round does not match local
         else ok true

------------------------------------------------------------------------------

processCertificatesM : Instant → LBFT Unit
processCertificatesM now = do
  syncInfo ← BlockStore.syncInfoM
  maybeSMP (RoundState.processCertificatesM now syncInfo) unit (processNewRoundEventM now)

------------------------------------------------------------------------------

processProposalM proposal = do
  s ← get
  let bs = rmGetBlockStore s
  vp ← ProposerElection.isValidProposalM proposal
  grd‖ is-nothing (proposal ^∙ bAuthor) ≔
       pure unit -- log: error: proposal does not have an author
     ‖ not vp ≔
       pure unit -- log: error: proposer for block is not valid for this round
     ‖ is-nothing (BlockStore.getQuorumCertForBlock (proposal ^∙ bParentId) bs) ≔
       pure unit -- log: error: QC of parent is not in BS
     ‖ not (maybeS (BlockStore.getBlock (proposal ^∙ bParentId) bs) false
           λ parentBlock →
             ⌊ (parentBlock ^∙ ebRound) <?ℕ (proposal ^∙ bRound) ⌋) ≔
       pure unit -- log: error: parentBlock < proposalRound
     ‖ otherwise≔
       (executeAndVoteM proposal >>= λ where
         (inj₁ _) → pure unit -- propagate error
         (inj₂ vote) → do
           RoundState.recordVote (unmetaVote vote) {- vote -}
           si ← BlockStore.syncInfoM
           recipient ← ProposerElection.getValidProposer
                       <$> use lProposerElection
                       <*> pure (proposal ^∙ bRound + 1)
           act (SendVote (VoteMsgWithMeta∙fromVoteWithMeta vote si) (recipient ∷ [])))
           -- TODO-1                                              {- mkNodesInOrder1 recipient-}

------------------------------------------------------------------------------

executeAndVoteM b =
  BlockStore.executeAndInsertBlockM b {- ∙^∙ logging -} ∙?∙ λ eb → do
  cr ← use (lRoundState ∙ rsCurrentRound)
  vs ← use (lRoundState ∙ rsVoteSent)
  so ← use lSyncOnly
  grd‖ is-just vs ≔
       bail unit -- already voted this round
     ‖ so ≔
       bail unit -- sync-only set
     ‖ otherwise≔ do
       let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
       SafetyRules.constructAndSignVoteM maybeSignedVoteProposal' {- ∙^∙ logging -}
         ∙?∙ λ vote → PersistentLivenessStorage.saveVoteM (unmetaVote vote)
         ∙?∙ λ _ → ok vote

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
    if v then continue else pure unit)
  else
    continue
 where
  continue : LBFT Unit
  continue = do
    let blockId = vote ^∙ vVoteData ∙ vdProposed ∙ biId
    s ← get
    let bs = _epBlockStore (_rmWithEC s)
    if true -- (is-just (BlockStore.getQuorumCertForBlock blockId {!!})) -- IMPL-TODO
      then pure unit
      else addVoteM now vote

addVoteM now vote = do
  s ← get
  let bs = _epBlockStore (_rmWithEC s)
  {- IMPL-TODO make this commented code work then remove the 'continue' after the comment
  maybeS nothing (bs ^∙ bsHighestTimeoutCert) continue λ tc →
    if-dec vote ^∙ vRound =? tc ^∙ tcRound
    then pure unit
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
    (inj₁ e)    → pure unit -- TODO : Haskell logs err and returns ().  Do we need to return error?
    (inj₂ unit) → processCertificatesM now

newTcAggregatedM now tc =
  BlockStore.insertTimeoutCertificateM tc >>= λ where
    (inj₁ e)    → pure unit -- TODO : Haskell logs err and returns ().  Do we need to return error?
    (inj₂ unit) → processCertificatesM now
