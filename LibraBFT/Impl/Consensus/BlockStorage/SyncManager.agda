{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockRetriever as BlockRetriever
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore     as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree      as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote         as Vote
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage   as PersistentLivenessStorage
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                       as String

module LibraBFT.Impl.Consensus.BlockStorage.SyncManager where

data NeedFetchResult : Set where
  QCRoundBeforeRoot QCAlreadyExist QCBlockExist NeedFetch : NeedFetchResult

------------------------------------------------------------------------------

fastForwardSyncM         : QuorumCert → BlockRetriever → LBFT (Either ErrLog RecoveryData)
fetchQuorumCertM         : QuorumCert → BlockRetriever → LBFT (Either ErrLog Unit)
insertQuorumCertM        : QuorumCert → BlockRetriever → LBFT (Either ErrLog Unit)
syncToHighestCommitCertM : QuorumCert → BlockRetriever → LBFT (Either ErrLog Unit)

------------------------------------------------------------------------------

needSyncForQuorumCert : QuorumCert → BlockStore → Either ErrLog Bool
needSyncForQuorumCert qc bs = maybeS (bs ^∙ bsRoot) (Left fakeErr) {-bsRootErrL here-} $ λ btr → Right
  (not (  BlockStore.blockExists (qc ^∙ qcCommitInfo ∙ biId) bs
        ∨ ⌊ btr ^∙ ebRound ≥?ℕ qc ^∙ qcCommitInfo ∙ biRound ⌋ ))
 where
  here' : List String.String → List String.String
  here' t = "SyncManager" ∷ "needSyncForQuorumCert" ∷ t

needFetchForQuorumCert : QuorumCert → BlockStore → Either ErrLog NeedFetchResult
needFetchForQuorumCert qc bs = maybeS (bs ^∙ bsRoot) (Left fakeErr) {-bsRootErrL here-} $ λ btr →
 grd‖ qc ^∙ qcCertifiedBlock ∙ biRound <?ℕ btr ^∙ ebRound                           ≔
      Right QCRoundBeforeRoot
    ‖ is-just (BlockStore.getQuorumCertForBlock (qc ^∙ qcCertifiedBlock ∙ biId) bs) ≔
      Right QCAlreadyExist
    ‖ BlockStore.blockExists (qc ^∙ qcCertifiedBlock ∙ biId) bs                     ≔
      Right QCBlockExist
    ‖ otherwise≔
      Right NeedFetch
 where
  here' : List String.String → List String.String
  here' t = "SyncManager" ∷ "needFetchForQuorumCert" ∷ t

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

------------------------------------------------------------------------------

loop1     : BlockRetriever → List Block → QuorumCert → LBFT (Either ErrLog (List Block))
loop2     : List Block → LBFT (Either ErrLog Unit)
hereFQCM' : List String.String → List String.String

fetchQuorumCertM qc retriever =
  loop1 retriever [] qc ∙?∙ loop2

-- TODO-1 PROVE IT TERMINATES
{-# TERMINATING #-}
loop1 retriever pending retrieveQC = do
    bs ← use lBlockStore
    if-RWST (BlockStore.blockExists (retrieveQC ^∙ qcCertifiedBlock ∙ biId) bs)
      then ok pending
      else
        BlockRetriever.retrieveBlockForQCM retriever retrieveQC 1
          ∙^∙ withErrCtx (hereFQCM' ("loop1" ∷ [])) ∙?∙ λ where
            (block ∷ []) → loop1 retriever (block ∷ pending) (block ^∙ bQuorumCert)
            (_ ∷ _ ∷ _)  → errorCase
            []           → errorCase
 where
  errorCase : LBFT (Either ErrLog (List Block))
  errorCase = do
              -- let msg = here ["loop1", "retrieveBlockForQCM returned more than asked for"]
              -- logErrExit msg
              bail fakeErr -- (ErrL msg)

loop2 = λ where
    [] -> ok unit
    (block ∷ bs) →
      BlockStore.insertSingleQuorumCertM (block ^∙ bQuorumCert)
        ∙^∙ withErrCtx (hereFQCM' ("loop2" ∷ [])) ∙?∙ \_ ->
          BlockStore.executeAndInsertBlockM block ∙?∙ \_ ->
            loop2 bs

hereFQCM' t = "SyncManager" ∷ "fetchQuorumCertM" ∷ t

------------------------------------------------------------------------------

syncToHighestCommitCertM highestCommitCert retriever = do
  bs ← use lBlockStore
  eitherS-RWST (needSyncForQuorumCert highestCommitCert bs) bail $ λ b →
    if not b
      then ok unit
      else
        fastForwardSyncM highestCommitCert retriever ∙?∙ \rd -> do
          logInfo fakeInfo -- (here ["fastForwardSyncM success", lsRD rd])
          BlockStore.rebuildM (rd ^∙ rdRoot) (rd ^∙ rdRootMetadata) (rd ^∙ rdBlocks) (rd ^∙ rdQuorumCerts)
            ∙^∙ withErrCtx (here' []) ∙?∙ λ _ -> do
            when-RWST (highestCommitCert ^∙ qcEndsEpoch) $ do
              me ← use (lRoundManager ∙ rmObmMe)
              -- TODO-1 : Epoch Change Proof
              -- let ecp = EpochChangeProof ∙ new [highestCommitCert ^∙ qcLedgerInfo] False
              logInfo fakeInfo -- (here ["fastForwardSyncM detected an EpochChange"])
              -- TODO-1 : uncomment this and remove pure unit when Epoch Change supported
              -- act (BroadcastEpochChangeProof lEC ecp (mkNodesInOrder1 me))
              pure unit
            ok unit
 where
  here' : List String.String → List String.String
  here' t = "SyncManager" ∷ "syncToHighestCommitCertM" ∷ t

------------------------------------------------------------------------------

fastForwardSyncM highestCommitCert retriever = do
  logInfo fakeInfo -- (here' [ "start state sync with peer", lsA (retriever^.brPreferredPeer)
                   --        , "to block", lsBI (highestCommitCert^.qcCommitInfo) ])
  BlockRetriever.retrieveBlockForQCM retriever highestCommitCert 3 ∙?∙ λ where
    blocks@(_ ∷ _ ∷ i ∷ []) ->
      if highestCommitCert ^∙ qcCommitInfo ∙ biId /= i ^∙ bId
      then bail fakeErr -- (here' [ "should have a 3-chain"
                        --        , lsHV (highestCommitCert^.qcCommitInfo.biId), lsHV (i^.bId) ]))
      else continue blocks
    x -> bail fakeErr -- (here' ["incorrect number of blocks returned", show (length x)]))

 where

  here' : List String.String → List String.String

  zipWithNatsFrom : {A : Set} → ℕ → List A → List (ℕ × A)
  zipWithNatsFrom n = λ where
    [] → []
    (x ∷ xs) → (n , x) ∷ zipWithNatsFrom (n + 1) xs

  checkBlocksMatchQCs : List QuorumCert → List (ℕ × Block) → LBFT (Either ErrLog Unit)

  continue : List Block → LBFT (Either ErrLog RecoveryData)
  continue blocks = do
    logInfo fakeInfo -- (here' (["received blocks"] <> fmap (lsHV . (^.bId)) blocks))
    let quorumCerts = highestCommitCert ∷ fmap (_^∙ bQuorumCert) blocks
    logInfo fakeInfo -- (here' (["quorumCerts"]     <> fmap (lsHV . (^.qcCommitInfo.biId)) quorumCerts))
    checkBlocksMatchQCs quorumCerts (zipWithNatsFrom 0 blocks)  ∙?∙ λ _ →
      PersistentLivenessStorage.saveTreeM blocks quorumCerts ∙?∙ λ _ → do
        -- TODO-1 : requires adding bsStorage to BlockStore
        -- use (lBlockStore ∙ bsStorage) >>= λ x → logInfo fakeInfo -- (here' ["XXX", lsPLS x])
        -- OBM NOT NEEDED: state_computer.sync_to
        -- This returns recovery data
        PersistentLivenessStorage.startM ∙^∙ withErrCtx (here' [])

  checkBlocksMatchQCs quorumCerts = λ where
    []                 → ok unit
    ((i , block) ∷ xs) →
      maybeS-RWST (quorumCerts !? i)
                  (bail fakeErr) -- (here' ["checkBlocksMatchQCs", "!?"])
                  $ λ qc →
      if-RWST (block ^∙ bId /= qc ^∙ qcCertifiedBlock ∙ biId)
      then (do
        logInfo fakeInfo -- [lsHV (block^.bId), lsB block]
        logInfo fakeInfo -- [lsHV (quorumCerts Prelude.!! i ^.qcCertifiedBlock.biId)
                         -- ,lsQC (quorumCerts Prelude.!! i)]
        bail fakeErr) -- (here' ("checkBlocksMatchQCs" ∷ "/=" ∷ []))
      else checkBlocksMatchQCs quorumCerts xs

  here' t = "SyncManager" ∷ "fastForwardSyncM" ∷ t

