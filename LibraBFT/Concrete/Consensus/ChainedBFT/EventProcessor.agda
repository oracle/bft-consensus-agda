{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockStore as BlockStore
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.OBM.Util

open RWST-do

module LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor where


 -- processCertificatesM
 -- processCommitM

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

  processProposalMsg : {a : Set} → Instant → ProposalMsg a → LBFT Unit
  processProposalMsg inst pm = return unit    -- TODO: just a placeholder for connecting handler

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

  processCommitM : {a : Set} → LedgerInfoWithSignatures → LBFT (List (ExecutedBlock a))
  processCommitM finalityProof
     with BlockStore.commitM finalityProof
  ...| blocksToCommit = {!!}
