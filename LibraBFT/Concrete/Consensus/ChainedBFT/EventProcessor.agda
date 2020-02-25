{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.OBM.Util
open import LibraBFT.Hash

open RWST-do

module LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open import LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockStore hash hash-cr as BlockStore


 -- processCertificatesM

 {-

  processCommitM
    :: (Monad m, RWBlockStore s a, RWBlockTree s a)
    => LedgerInfoWithSignatures
    -> LBFT m e s a ()
  processCommitM finalityProof =
    logEE ["EventProcessor", "processCommitM", lsLIWS finalityProof] $ do
    blocksToCommit <- BlockStore.commitM finalityProof
    forM_ blocksToCommit $ \eb ->
      logInfo (InfoCommitting eb)

 -}

  processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
  processCommitM finalityProof
     with BlockStore.commitM finalityProof
  ...| blocksToCommit = {!!}


 {-
  processProposalMsgM
    :: ( Monad m, Eq a, Show a, S.Serialize a, RWValidatorVerifier s
       , RWEventProcessor s a, RWPacemaker s, RWBlockStore s a, RWBlockTree s a, RWSafetyRules s
       , RWProposerElection s, RWProposalGenerator s a, RWValidatorSigner s, RWPersistentStorage s )
    => Instant -> ProposalMsg a
    -> LBFT m e s a ()
  processProposalMsgM now m =
    logEE ["EventProcessor", "processProposalMsgM", lsPM m] $
    maybeMP (preProcessProposalM now m) () processProposedBlockM
 -}

  processProposalMsg : Instant → ProposalMsg → LBFT Unit
  processProposalMsg inst pm = pure unit    -- TODO: just a placeholder for connecting handler

 {-
  processVoteM
    :: ( Monad m, Eq a, S.Serialize a, RWEventProcessor s a, RWPacemaker s
       , RWBlockStore s a, RWBlockTree s a, RWPersistentStorage s, RWSafetyRules s
       , RWProposerElection s, RWProposalGenerator s a, RWValidatorVerifier s )
    => Instant -> VoteMsg
    -> LBFT m e s a ()
 -}

  processVote : Instant → VoteMsg → LBFT Unit
  processVote now msg = pure unit  -- TODO: just a placeholder for connecting handler
