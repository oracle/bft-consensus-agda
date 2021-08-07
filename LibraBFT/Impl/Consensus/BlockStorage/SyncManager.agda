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

------------------------------------------------------------------------------
postulate

  needFetchForQuorumCert
    : QuorumCert → BlockStore
    → Either ErrLog NeedFetchResult

  fetchQuorumCertM
    : QuorumCert → BlockRetriever
    → LBFT (Either ErrLog Unit)

  syncToHighestCommitCertM
    : QuorumCert → BlockRetriever
    → LBFT (Either ErrLog Unit)

insertQuorumCertM : QuorumCert → BlockRetriever → LBFT (Either ErrLog Unit)

------------------------------------------------------------------------------

addCertsM : SyncInfo → BlockRetriever → LBFT (Either ErrLog Unit)
addCertsM {-reason-} syncInfo retriever =
  syncToHighestCommitCertM     (syncInfo ^∙ siHighestCommitCert) retriever ∙?∙ \_ ->
  insertQuorumCertM {-reason-} (syncInfo ^∙ siHighestCommitCert) retriever ∙?∙ \_ ->
  insertQuorumCertM {-reason-} (syncInfo ^∙ siHighestQuorumCert) retriever ∙?∙ \_ ->
  maybeS-RWST                  (syncInfo ^∙ siHighestTimeoutCert) (ok unit) $
    \tc -> BlockStore.insertTimeoutCertificateM tc

------------------------------------------------------------------------------

module insertQuorumCertM (qc : QuorumCert) (retriever : BlockRetriever) where
  step₀ :                         LBFT (Either ErrLog Unit)
  step₁ : BlockStore            → LBFT (Either ErrLog Unit)
  step₁-else :                    LBFT (Either ErrLog Unit)
  step₂ : ExecutedBlock         → LBFT (Either ErrLog Unit)
  step₃ :                         LBFT (Either ErrLog Unit)

  step₀ = do
    bs ← use lBlockStore
    _ ← caseM⊎ needFetchForQuorumCert qc bs of λ where
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
    step₁ bs

  step₁ bs = do
    maybeS-RWST (bs ^∙ bsRoot) (bail fakeErr) $ λ bsr →
      if-RWST (bsr ^∙ ebRound) <?ℕ (qc ^∙ qcCommitInfo ∙ biRound)
        then step₂ bsr
        else
          step₁-else

  step₂ bsr = do
          let finalityProof = qc ^∙ qcLedgerInfo
          BlockStore.commitM finalityProof ∙?∙ λ xx →
            step₃

  step₃ = do
            if-RWST qc ^∙ qcEndsEpoch
              then ok unit -- TODO-1 EPOCH CHANGE
              else ok unit

  step₁-else =
          ok unit

insertQuorumCertM = insertQuorumCertM.step₀

