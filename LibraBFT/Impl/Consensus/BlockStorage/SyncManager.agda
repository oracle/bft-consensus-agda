{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore   as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree    as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.SyncManager where

data NeedFetchResult : Set where
  QCRoundBeforeRoot QCAlreadyExist QCBlockExist NeedFetch : NeedFetchResult

postulate

  fetchQuorumCertM
    : QuorumCert → BlockRetriever
    → LBFT (Either ErrLog Unit)

  needFetchForQuorumCert
    : QuorumCert → BlockStore
    → Either ErrLog NeedFetchResult

------------------------------------------------------------------------------

insertQuorumCertM
  : QuorumCert → BlockRetriever
  → LBFT (Either ErrLog Unit)
insertQuorumCertM qc retriever = do
  bs ← use lBlockStore
  _ ← case needFetchForQuorumCert qc bs of λ where
    (Left e) →
      bail e
    (Right NeedFetch) →
      fetchQuorumCertM qc retriever
      ∙^∙ withErrCtx ("" ∷ [])
    (Right QCBlockExist) →
      BlockStore.insertSingleQuorumCertM qc ∙^∙ withErrCtx ("" ∷ []) ∙?∙ λ _ → do
      use lBlockStore >>= const (logInfo fakeInfo) -- InfoBlockStoreShort (here [lsQC qc])
      ok unit
    (Right _) →
      ok unit
  maybeS (bs ^∙ bsRoot) (bail fakeErr) $ λ bsr →
    ifM (bsr ^∙ ebRound) <?ℕ (qc ^∙ qcCommitInfo ∙ biRound)
      then (do
        let finalityProof = qc ^∙ qcLedgerInfo
        BlockStore.commitM finalityProof ∙?∙ λ xx →
          ifM qc ^∙ qcEndsEpoch
            then ok unit -- TODO-1 EPOCH CHANGE
            else ok unit)
      else
        ok unit

