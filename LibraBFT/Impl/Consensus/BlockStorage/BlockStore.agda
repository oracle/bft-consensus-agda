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
------------------------------------------------------------------------------
import      Data.String                                          as String

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

------------------------------------------------------------------------------

getBlock : HashValue → BlockStore → Maybe ExecutedBlock

executeAndInsertBlockE : BlockStore → Block → Either ErrLog (BlockStore × ExecutedBlock)

executeBlockE
  : BlockStore → Block
  → Either ErrLog ExecutedBlock

executeBlockE₀
  : BlockStore → Block
    → EitherD ErrLog ExecutedBlock

pathFromRoot
  : HashValue → BlockStore
  → Either ErrLog (List ExecutedBlock)

pathFromRootM
  : HashValue
  → LBFT (Either ErrLog (List ExecutedBlock))

------------------------------------------------------------------------------

postulate
  build
    : RootInfo      → RootMetadata
    → List Block    → List QuorumCert           → Maybe TimeoutCertificate
    → {-StateComputer →-} PersistentLivenessStorage → Usize
    → Either ErrLog BlockStore

------------------------------------------------------------------------------

commitM
  : LedgerInfoWithSignatures
  → LBFT (Either ErrLog Unit)
commitM finalityProof = do
  bs ← use lBlockStore
  maybeSD (bs ^∙ bsRoot) (bail fakeErr) $ λ bsr → do
    let blockIdToCommit = finalityProof ^∙ liwsLedgerInfo ∙ liConsensusBlockId
    case getBlock blockIdToCommit bs of λ where
      nothing →
        bail (ErrBlockNotFound blockIdToCommit)
      (just blockToCommit) →
        ifD‖ blockToCommit ^∙ ebRound ≤?ℕ bsr ^∙ ebRound ≔
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

rebuildM : RootInfo → RootMetadata → List Block → List QuorumCert → LBFT (Either ErrLog Unit)
rebuildM root rootMetadata blocks quorumCerts = do
  -- logEE lEC (here []) $ do
  self0 ← use lBlockStore
  case build
         root rootMetadata blocks quorumCerts
         (self0 ^∙ bsHighestTimeoutCert)
         --(self0 ^∙ bsStateComputer) -- the agda code does not have a state computer (yet?)
         (self0 ^∙ bsStorage)
         (self0 ^∙ bsInner ∙ btMaxPrunedBlocksInMem) of λ where
    (Left  e)    → bail e
    (Right (BlockStore∙new inner _)) → do
      toRemove ← BlockTree.getAllBlockIdM
      PersistentLivenessStorage.pruneTreeM toRemove ∙?∙  λ _ → do
       lRoundManager ∙ rmBlockStore ∙ bsInner ∙= inner
       self1 ← use lBlockStore
       maybeS (self1 ^∙ bsRoot) (bail fakeErr {-bsRootErrL here-}) $ λ bsr → do
        ifD self1 ^∙ bsHighestCommitCert ∙ qcCommitInfo ∙ biRound >? bsr ^∙ ebRound
          then
            (commitM (self1 ^∙ bsHighestCommitCert ∙ qcLedgerInfo) ∙^∙
              withErrCtx (here' ("commitM failed" ∷ [])) ∙?∙  λ _ →
              ok unit)
          else ok unit
 where
  here' : List String.String → List String.String
  here' t =
    "BlockStore" ∷ "rebuildM" ∷ t
    -- lsRI root : lsRMD rootMetadata : lsBs blocks : lsQCs quorumCerts : t

------------------------------------------------------------------------------

executeAndInsertBlockM : Block → LBFT (Either ErrLog ExecutedBlock)
executeAndInsertBlockM b = do
  bs ← use lBlockStore
  case⊎D executeAndInsertBlockE bs b of λ where
    (Left e) → bail e
    (Right (bs' , eb)) → do
      lBlockStore ∙= bs'
      ok eb

module executeAndInsertBlockE (bs0 : BlockStore) (block : Block) where
  step₀ : EitherD ErrLog (BlockStore × ExecutedBlock)
  step₂ continue : EitherD ErrLog (BlockStore × ExecutedBlock)
  continue = step₂
  step₃ : ExecutedBlock → EitherD ErrLog (BlockStore × ExecutedBlock)
  step₄ : ExecutedBlock → EitherD ErrLog (BlockStore × ExecutedBlock)
  step₅ : (bsr eb : ExecutedBlock) → EitherD ErrLog (BlockStore × ExecutedBlock)
  step₆ : (bsr eb : ExecutedBlock) → EitherD ErrLog (BlockStore × ExecutedBlock)

  step₀ =
    maybeSD (getBlock (block ^∙ bId) bs0) continue (pure ∘ (bs0 ,_))

  here' : List String.String → List String.String
  here' t = "BlockStore" ∷ "executeAndInsertBlockE" {-∷ lsB block-} ∷ t

  step₂ =
      maybeSD (bs0 ^∙ bsRoot) (LeftD fakeErr) step₃

  step₃ bsr =
      let btRound = bsr ^∙ ebRound in
      ifD btRound ≥?ℕ block ^∙ bRound
      then LeftD fakeErr -- block with old round
      else step₄ bsr

  step₄ bsr = do
        eb ← case executeBlockE bs0 block of λ where
          (Right res) → RightD res
          (Left (ErrBlockNotFound parentBlockId)) →
            eitherS (pathFromRoot parentBlockId bs0) LeftD $ λ blocksToReexecute →
              case (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
                (Left  e) → LeftD e
                (Right _) → executeBlockE₀ bs0 block -- NOTE: `executeBlockE₀` is used here because we want an `EitherD ErrLog ExecutedBlock`
          (Left err) → LeftD err
        step₅ bsr eb

  step₅ bsr eb = do
        bs1 ← withErrCtxD'
                (here' [])
                -- TODO-1 : use inspect qualified so Agda List singleton can be in scope.
                (PersistentLivenessStorage.saveTreeE bs0 ((eb ^∙ ebBlock) ∷ []) [])
        step₆ bsr eb

  step₆ bsr eb = do
        (bt' , eb') ← fromEither $ BlockTree.insertBlockE eb (bs0 ^∙ bsInner) -- TODO-1: make this `BlockTree.insertBlockE₀`
        pure ((bs0 & bsInner ∙~  bt') , eb')

executeAndInsertBlockE bs0 block = EitherD-run $ executeAndInsertBlockE.step₀ bs0 block

executeBlockE bs block =
  if is-nothing (getBlock (block ^∙ bParentId) bs)
    then Left (ErrBlockNotFound {-(here ["block with missing parent"])-} (block ^∙ bParentId))
    else {- do
      let compute            = bs ^. bsStateComputer.scCompute
          stateComputeResult = compute (bs^.bsStateComputer) block (block^.bParentId) -}
      pure (ExecutedBlock∙new block stateComputeResult)

executeBlockE₀ bs block = fromEither $ executeBlockE bs block

------------------------------------------------------------------------------

insertSingleQuorumCertE
  : BlockStore → QuorumCert
  → Either ErrLog (BlockStore × List InfoLog)

insertSingleQuorumCertM
  : QuorumCert
  → LBFT (Either ErrLog Unit)
insertSingleQuorumCertM qc = do
  bs ← use lBlockStore
  case insertSingleQuorumCertE bs qc of λ where
    (Left  e)   → bail e
    (Right (bs' , info)) → do
      forM_ info logInfo
      lBlockStore ∙= bs'
      ok unit

insertSingleQuorumCertE bs qc =
  maybeS (getBlock (qc ^∙ qcCertifiedBlock ∙ biId) bs)
         (Left (ErrBlockNotFound
                  -- (here ["insert QC without having the block in store first"])
                  (qc ^∙ qcCertifiedBlock ∙ biId)))
         (λ executedBlock →
             if ExecutedBlock.blockInfo executedBlock /= qc ^∙ qcCertifiedBlock
             then Left fakeErr
 --                      (ErrL (here [ "QC for block has different BlockInfo than EB"
 --                                  , "QC certified BI", show (qc^.qcCertifiedBlock)
 --                                  , "EB BI", show (ExecutedBlock.blockInfo executedBlock)
 --                                  , "EB", show executedBlock ]))

             else (do
                    bs'           ← withErrCtx' (here' [])
                                      (PersistentLivenessStorage.saveTreeE bs [] (qc ∷ []))
                    (bt , output) ← BlockTree.insertQuorumCertE qc (bs' ^∙ bsInner)
                    pure ((bs' & bsInner ∙~ bt) , output)))
 where
  here' : List String.String → List String.String
  here' t = "BlockStore" ∷ "insertSingleQuorumCertE" ∷ t

------------------------------------------------------------------------------

insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either ErrLog Unit)
insertTimeoutCertificateM tc = do
  curTcRound ← maybeHsk {-(Round-} 0 {-)-} (_^∙ tcRound) <$> use (lBlockStore ∙ bsHighestTimeoutCert)
  ifD tc ^∙ tcRound ≤?ℕ curTcRound
    then ok unit
    else
      PersistentLivenessStorage.saveHighestTimeoutCertM tc ∙^∙ withErrCtx ("" ∷ []) ∙?∙ λ _ → do
        BlockTree.replaceTimeoutCertM tc
        ok unit

------------------------------------------------------------------------------

blockExists : HashValue → BlockStore → Bool
blockExists hv bs = Map.kvm-member hv (bs ^∙ bsInner ∙ btIdToBlock)

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
               <*> use (lBlockStore ∙ bsHighestTimeoutCert)
