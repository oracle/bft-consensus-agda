open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockStore as BlockStore
open import LibraBFT.Concrete.Consensus.Types

module LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor where


 -- processCertificatesM
 -- processCommitM

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
  processCommitM finalityProof {state₀}
     with BlockStore.commitM finalityProof {state₀}
  ...| blocksToCommit = {!!}

  -- TODO: logging - do it like state, pass in cummulative logs and cummulative actions
  --       actions - send a commit message (Haskell code doesn't do it; to discuss)
