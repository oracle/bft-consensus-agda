{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
import      LibraBFT.Impl.Consensus.Liveness.RoundState          as RoundState
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore      as BlockStore
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection    as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage    as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules      as SafetyRules
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId


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

  fakeProcessProposalMsg : Instant → ProposalMsg → LBFT Unit
  fakeProcessProposalMsg inst pm = do
    st ← get
    xx ← use rmHighestQC   -- Not used; just a demonstration that our RoundManager-specific "use" works
    rmHighestQC ∙= xx -- Similarly for modify'
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
        mvs = VoteWithMeta∙new sv mvsNew -- Tracking the source of the vote
        bt = rmw ^∙ (lBlockTree 𝓔)
        si = SyncInfo∙new (₋btHighestQuorumCert bt) (₋btHighestCommitCert bt)
        rm' = rm [ rmLastVotedRound := nr ]
        st' = RoundManager∙new rm' (RoundManagerEC-correct-≡ (₋rmEC st) rm' refl rmc)
                                   (subst RoundManagerWithEC (α-EC-≡ rm rm' refl refl rmc) rmw)
    put st'
    tell1 (SendVote (VoteMsgWithMeta∙fromVoteWithMeta mvs si) (fakeAuthor ∷ []))
    pure unit

  processVote : Instant → VoteMsg → LBFT Unit
  processVote now msg = pure unit

  ------------------------------------------------------------------------------
  syncUpM : Instant → SyncInfo → Author → LBFT (ErrLog ⊎ Unit)
  ensureRoundAndSyncUpM : Instant → Round → SyncInfo → Author → Bool →
                          LBFT (ErrLog ⊎ Bool)
  processProposalM : Block → LBFT Unit
  executeAndVoteM : Block → LBFT (ErrLog ⊎ VoteWithMeta)

  -- external entry point
  -- TODO-2: The sync info that the peer requests if it discovers that its round
  -- state is behind the sender's should be sent as an additional argument, for now.
  processProposalMsgM : Instant → {- Author → -} ProposalMsg → LBFT Unit
  processProposalMsgM now pm = do
    caseMM pm ^∙ pmProposer of λ where
      nothing →
        return unit -- log: info: proposal with no author
      (just pAuthor) → do
        _r ← ensureRoundAndSyncUpM now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo) pAuthor true
        caseM⊎ _r of λ where
          (inj₁ _) → return unit -- log: error: <propagate error>
          (inj₂ b) →
            ifM b
              then processProposalM (pm ^∙ pmProposal)
              else do
                currentRound ← use (lRoundState ∙ rsCurrentRound)
                return unit -- log: info: dropping proposal for old round

  syncUpM now syncInfo author = ok unit

  -- ensureRoundAndSyncUp
  -----------------------

  ensureRoundAndSyncUpM-check₁ : Instant → Round → SyncInfo → Author → Bool →
                                 LBFT (ErrLog ⊎ Bool)
  ensureRoundAndSyncUpM-check₁-cont : Round → Unit → LBFT (ErrLog ⊎ Bool)

  ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote = do
    currentRound ← use (lRoundState ∙ rsCurrentRound)
    if ⌊ messageRound <? currentRound ⌋
      then ok false
      else ensureRoundAndSyncUpM-check₁ now messageRound syncInfo author helpRemote

  ensureRoundAndSyncUpM-check₁ now messageRound syncInfo author helpRemote = do
    syncUpM now syncInfo author ∙?∙ ensureRoundAndSyncUpM-check₁-cont messageRound

  ensureRoundAndSyncUpM-check₁-cont messageRound = λ _ → do
    currentRound' ← use (lRoundState ∙ rsCurrentRound)
    if not ⌊ messageRound ≟ℕ currentRound' ⌋
      then bail unit  -- error: after sync, round does not match local
      else ok true

  -- processProposalM
  -------------------
  module ProcessProposalM (proposal : Block) where
    step₀ : LBFT Unit
    step₁ : ∀ {pre} → BlockStore (α-EC-RM pre) → Bool → LBFT Unit
    step₂ : LBFT Unit
    step₃ : VoteWithMeta → LBFT Unit

    step₀ = do
      _rm ← get
      let bs = rmGetBlockStore _rm
      vp ← ProposerElection.isValidProposalM proposal
      step₁{_rm} bs vp
    step₁ bs vp =
      ifM‖ is-nothing (proposal ^∙ bAuthor)
           ≔ pure unit -- log: error: proposal does not have an author
         ‖ not vp
           ≔ pure unit -- log: error: proposer for block is not valid for this round
         ‖ is-nothing (BlockStore.getQuorumCertForBlock (proposal ^∙ bParentId) bs)
           ≔ pure unit -- log: error: QC of parent is not in BS
         ‖ not (maybeS (BlockStore.getBlock (proposal ^∙ bParentId) bs) false
                  λ parentBlock →
                  ⌊ (parentBlock ^∙ ebRound) <?ℕ (proposal ^∙ bRound) ⌋)
           ≔ pure unit -- log: error: parentBlock < proposalRound
         ‖ otherwise≔ step₂
    step₂ = do
            _r ← executeAndVoteM proposal
            caseM⊎ _r of λ where
              (inj₁ _) → pure unit -- propagate error
              (inj₂ vote) → step₃ vote
    step₃ vote = do
                RoundState.recordVote (unmetaVote vote) {- vote -}
                si ← BlockStore.syncInfo
                recipient ← ProposerElection.getValidProposer
                              <$> use lProposerElection
                              <*> pure (proposal ^∙ bRound + 1)
                act (SendVote (VoteMsgWithMeta∙fromVoteWithMeta vote si)
                              (recipient ∷ []))
                -- TODO-1   {- mkNodesInOrder1 recipient-}

  processProposalM = ProcessProposalM.step₀

  -- executeAndVoteM
  module ExecuteAndVoteM (b : Block) where
    step₀ :                 LBFT (ErrLog ⊎ VoteWithMeta)
    step₁ : ExecutedBlock → LBFT (ErrLog ⊎ VoteWithMeta)
    step₂ : ExecutedBlock → LBFT (ErrLog ⊎ VoteWithMeta)
    step₃ : VoteWithMeta  → LBFT (ErrLog ⊎ VoteWithMeta)

    step₀ = BlockStore.executeAndInsertBlockM b ∙?∙ step₁
    step₁ eb = do
      cr ← use (lRoundState ∙ rsCurrentRound)
      vs ← use (lRoundState ∙ rsVoteSent)
      so ← use lSyncOnly
      ifM‖ is-just vs
           ≔ bail unit -- already voted this round
         ‖ so
           ≔ bail unit -- sync-only set
         ‖ otherwise≔ step₂ eb
    step₂ eb = do
           let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
           SafetyRules.constructAndSignVoteM maybeSignedVoteProposal' {- ∙^∙ logging -}
             ∙?∙ step₃
    step₃ vote =
                 PersistentLivenessStorage.saveVoteM (unmetaVote vote)
             ∙?∙ λ _ → ok vote

  executeAndVoteM = ExecuteAndVoteM.step₀
