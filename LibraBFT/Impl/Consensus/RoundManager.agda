{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore   as BlockStore
open import LibraBFT.Impl.Consensus.BlockStorage.SyncManager  as SyncManager
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection as ProposerElection
open import LibraBFT.Impl.Consensus.Liveness.RoundState       as RoundState hiding (processCertificatesM)
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Prelude
open import Optics.All


-- This is a minimal/fake example handler that obeys the VotesOnce rule, enabling us to start
-- exploring how we express the algorithm and prove properties about it.  It simply sends a vote for
-- 1 + its LatestVotedRound, and increments its LatestVotedRound.  It is called RoundManager for
-- historical reasons, because this what a previous version of LibraBFT called its main handler;
-- this will be updated when we move towards modeling a more recent implementation.

module LibraBFT.Impl.Consensus.RoundManager where

open RWST-do

processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
processCommitM finalityProof = pure []

fakeAuthor : Author
fakeAuthor = 0

fakeBlockInfo : Epoch → Round → ProposalMsg → BlockInfo
fakeBlockInfo eid rnd pm = BlockInfo∙new eid rnd (pm ^∙ pmProposal ∙ bId)

fakeLedgerInfo : BlockInfo → ProposalMsg → LedgerInfo
fakeLedgerInfo bi pm = LedgerInfo∙new bi (pm ^∙ pmProposal ∙ bId)

postulate -- TODO-1: these are temporary scaffolding for the fake implementation
  fakeSK  : SK
  fakeSig : Signature

processProposalMsg : Instant → ProposalMsg → LBFT Unit
processProposalMsg inst pm = do
  st ← get
  xx ← use rmHighestQC   -- Not used; just a demonstration that our RoundManager-specific "use" works
  modify' rmHighestQC xx -- Similarly for modify'
  let RoundManager∙new rm rmc rmw = st
      𝓔  = α-EC (rm , rmc)
      e  = rm ^∙ rmEpoch
      nr = suc (rm ^∙ rmLastVotedRound)
      uv = Vote∙new
                  (VoteData∙new (fakeBlockInfo e nr pm) (fakeBlockInfo e 0 pm))
                  fakeAuthor
                  (fakeLedgerInfo (fakeBlockInfo e nr pm) pm)
                  fakeSig
                  nothing
      sv = record uv { ₋vSignature = sign ⦃ sig-Vote ⦄ uv fakeSK}
      bt = rmw ^∙ (lBlockTree 𝓔)
      si = SyncInfo∙new (₋btHighestQuorumCert bt) (₋btHighestCommitCert bt)
      rm' = rm [ rmLastVotedRound := nr ]
      st' = RoundManager∙new rm' (RoundManagerEC-correct-≡ (₋rmEC st) rm' refl rmc)
                                 (subst RoundManagerWithEC (α-EC-≡ rm rm' refl refl rmc) rmw)
  put st'
  tell1 (SendVote (VoteMsg∙new sv si) (fakeAuthor ∷ []))
  pure unit

processVote : Instant → VoteMsg → LBFT Unit
processVote now msg = pure unit

------------------------------------------------------------------------------

processNewRoundEventM : Instant → NewRoundEvent → LBFT Unit
processNewRoundEventM now nre = pure unit

------------------------------------------------------------------------------

processCertificatesM : Instant → LBFT Unit
processCertificatesM now = do
  syncInfo ← BlockStore.syncInfoM
  maybeSMP (RoundState.processCertificatesM now syncInfo) unit (processNewRoundEventM now)

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
    let bs = ₋epBlockStore (₋rmWithEC s)
    if true -- (is-just (BlockStore.getQuorumCertForBlock blockId {!!})) -- IMPL-TODO
      then pure unit
      else addVoteM now vote

addVoteM now vote = do
  s ← get
  let bs = ₋epBlockStore (₋rmWithEC s)
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
    let verifier = ₋esVerifier (₋rmEpochState (₋rmEC rm))
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
