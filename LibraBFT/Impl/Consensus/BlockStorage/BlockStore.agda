{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap                                  as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree       as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage    as PersistentLivenessStorage
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

------------------------------------------------------------------------------

getBlock : HashValue → BlockStore → Maybe ExecutedBlock

executeAndInsertBlockE : BlockStore → Block → Either ErrLog (BlockStore × ExecutedBlock)

executeBlockE
  : BlockStore → Block
  → Either ErrLog ExecutedBlock

pathFromRoot
  : HashValue → BlockStore
  → Either ErrLog (List ExecutedBlock)

pathFromRootM
  : HashValue
  → LBFT (Either ErrLog (List ExecutedBlock))

------------------------------------------------------------------------------

commitM
  : LedgerInfoWithSignatures
  → LBFT (Either ErrLog Unit)
commitM finalityProof = do
  bs ← use lBlockStore
  maybeS (bs ^∙ bsRoot) (bail fakeErr) $ λ bsr → do
    let blockIdToCommit = finalityProof ^∙ liwsLedgerInfo ∙ liConsensusBlockId
    case getBlock blockIdToCommit bs of λ where
      nothing →
        bail (ErrBlockNotFound blockIdToCommit)
      (just blockToCommit) →
        ifM‖ blockToCommit ^∙ ebRound ≤?ℕ bsr ^∙ ebRound ≔
             bail fakeErr -- "commit block round lower than root"
           ‖ otherwise≔ (pathFromRootM blockIdToCommit >>= λ where
                           (Left  e) → bail e
                           (Right r) → continue blockToCommit r)
 where
  continue : ExecutedBlock → List ExecutedBlock → LBFT (Either ErrLog Unit)
  continue blockToCommit blocksToCommit = do
    -- NOTE: Haskell tells the "StateComputer" to commit 'blocksToCommit'.
    -- TODO-1: The StateComputer might indicate an epoch change.
    -- NO NEED FOR PRUNING: pruneTreeM blockToCommit
    --
    -- THIS IS WHERE COMMIT IS COMPLETED.
    -- To connect to the proof's correctness condition, it will be necessary to
    -- send a CommitMsg, which will carry evidence of the CommitRule
    -- needed to invoke correctness conditions like ConcCommitsDoNotConflict*.
    -- The details of this connection yet have not been settled yet.
    -- TODO-1: Once the details are determined, then make the connection.
    ok unit

------------------------------------------------------------------------------

executeAndInsertBlockM : Block → LBFT (Either ErrLog ExecutedBlock)
executeAndInsertBlockM b = do
  bs ← use lBlockStore
  caseM⊎ executeAndInsertBlockE bs b of λ where
    (Left e) → bail e
    (Right (bs' , eb)) → do
      lBlockStore ∙= bs'
      ok eb

executeAndInsertBlockE bs0 block =
  maybeS (getBlock (block ^∙ bId) bs0) continue (pure ∘ (bs0 ,_))
 where
  continue : Either ErrLog (BlockStore × ExecutedBlock)
  continue =
    maybeS (bs0 ^∙ bsRoot) (Left fakeErr) λ bsr →
    let btRound = bsr ^∙ ebRound in
    if-dec btRound ≥?ℕ block ^∙ bRound
    then Left fakeErr -- block with old round
    else do
      eb ← case executeBlockE bs0 block of λ where
        (Right res) → Right res
        (Left (ErrBlockNotFound parentBlockId)) → do
          eitherS (pathFromRoot parentBlockId bs0) Left $ λ blocksToReexecute →
            case (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
              (Left  e) → Left e
              (Right _) → executeBlockE bs0 block
        (Left err) → Left err
      bs1 ← {-withErrCtx' (here [])-}
            -- TODO-1 : use inspect qualified so Agda List singleton can be in scope.
            (PersistentLivenessStorage.saveTreeE bs0 ((eb ^∙ ebBlock) ∷ []) [])
      (bt' , eb') ← BlockTree.insertBlockE eb (bs0 ^∙ bsInner)
      pure ((bs0 & bsInner ∙~  bt') , eb')

executeBlockE bs block =
  if is-nothing (getBlock (block ^∙ bParentId) bs)
    then Left (ErrBlockNotFound {-(here ["block with missing parent"])-} (block ^∙ bParentId))
    else {- do
      let compute            = bs ^. bsStateComputer.scCompute
          stateComputeResult = compute (bs^.bsStateComputer) block (block^.bParentId) -}
      pure (ExecutedBlock∙new block stateComputeResult)

------------------------------------------------------------------------------

insertSingleQuorumCertE
  : BlockStore → QuorumCert
  → Either ErrLog BlockStore {- Haskell returns ([InfoLog a], BlockStore a)-}

insertSingleQuorumCertM
  : QuorumCert
  → LBFT (Either ErrLog Unit)
insertSingleQuorumCertM qc = do
  bs ← use lBlockStore
  case insertSingleQuorumCertE bs qc of λ where
    (Left  e)   → bail e
    (Right bs') → do
      lBlockStore ∙= bs'
      ok unit

insertSingleQuorumCertE bs qc =
  maybeS (getBlock (qc ^∙ qcCertifiedBlock ∙ biId) bs)
         (Left (ErrBlockNotFound
                  -- (here ["insert QC without having the block in store first"])
                  (qc ^∙ qcCertifiedBlock ∙ biId)))
         (λ executedBlock ->
             if ExecutedBlock.blockInfo executedBlock /= qc ^∙ qcCertifiedBlock
             then Left fakeErr
 --                      (ErrL (here [ "QC for block has different BlockInfo than EB"
 --                                  , "QC certified BI", show (qc^.qcCertifiedBlock)
 --                                  , "EB BI", show (ExecutedBlock.blockInfo executedBlock)
 --                                  , "EB", show executedBlock ]))

             else (do
                    bs' ← {-withErrCtx' (here [])-}
                          (PersistentLivenessStorage.saveTreeE bs [] (qc ∷ []))
                    bt  ← BlockTree.insertQuorumCertE qc (bs' ^∙ bsInner)
                    pure (bs' & bsInner ∙~ bt)))

------------------------------------------------------------------------------

insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either ErrLog Unit)
insertTimeoutCertificateM tc = do
  curTcRound ← maybeHsk {-(Round-} 0 {-)-} (_^∙ tcRound) <$> use (lBlockStore ∙ bsHighestTimeoutCert)
  ifM tc ^∙ tcRound ≤?ℕ curTcRound
    then ok unit
    else
      PersistentLivenessStorage.saveHighestTimeoutCertM tc ∙^∙ withErrCtxt ∙?∙ λ _ → do
        BlockTree.replaceTimeoutCertM tc
        ok unit

------------------------------------------------------------------------------

getBlock hv bs = btGetBlock hv (bs ^∙ bsInner)

getQuorumCertForBlock : HashValue → BlockStore → Maybe QuorumCert
getQuorumCertForBlock hv bs = Map.lookup hv (bs ^∙ bsInner ∙ btIdToQuorumCert)

pathFromRootM hv = pathFromRoot hv <$> use lBlockStore

pathFromRoot hv bs = BlockTree.pathFromRoot hv (bs ^∙ bsInner)

------------------------------------------------------------------------------

syncInfoM : LBFT SyncInfo
syncInfoM =
  SyncInfo∙new <$> use (lBlockStore ∙ bsHighestQuorumCert)
               <*> use (lBlockStore ∙ bsHighestCommitCert)
