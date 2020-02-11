open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Records
import      LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree as BlockTree

module LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockStore where

  getBlock : {a : Set} → HashValue -> BlockStore a -> Maybe (ExecutedBlock a)
  getBlock hv bs = btGetBlock hv (bsInner bs)

  {-
  commitM
    :: (Monad m, RWBlockStore s a, RWBlockTree s a)
    => LedgerInfoWithSignatures
    -> LBFT m e s a [ExecutedBlock a]
  commitM finalityProof = do
    bs <- use lBlockStore
    let blockIdToCommit = finalityProof^.liwsLedgerInfo.liConsensusBlockId
    case getBlock blockIdToCommit bs of
      Nothing -> do
        logErr (ErrBlockNotFound
                 (here ["committed block id not found", lsLIWS finalityProof])
                 blockIdToCommit)
        pure []
      Just blockToCommit | blockToCommit^.ebRound <= bs^.bsRoot.ebRound -> do
        logErrL (here [ "commit block round lower than root"
                      , show (bs^.bsRoot.ebRound), lsLIWS finalityProof ])
        pure []
      Just blockToCommit -> do
        blocksToCommit <- pathFromRootM blockIdToCommit >>= \case
          Nothing -> pure []
          Just x  -> pure x
        -- TODO StateComputer.commit
        pruneTreeM (blockToCommit^.ebId)
        pure blocksToCommit
   where
    here t = "BlockStore":"commitM":t
  -}

  pathFromRootM : HashValue → LBFT (Maybe (List (ExecutedBlock TX)))
  pathFromRootM = BlockTree.pathFromRootM

  pruneTreeM : HashValue -> LBFT Unit
  pruneTreeM _ {state₀} = unit , state₀ , []
    -- TODO prune
    -- BlockTree.processPrunedBlocksM

  commitM : LedgerInfoWithSignatures → LBFT (List (ExecutedBlock TX))
  commitM finalityProof {state₀} {acts₀}
    with use lBlockStore {state₀}
  ...| bs
    with (liConsensusBlockId ∘ liwsLedgerInfo) finalityProof
  ...| blockIdToCommit
    with getBlock {TX} blockIdToCommit bs
  ...| nothing = [] , state₀ , []
  ...| just blockToCommit
    with ebRound blockToCommit ≤? ebRound (bsRoot bs)
  ...| yes _ = [] , state₀ , (LogErr "commit block round lower than root") ∷ acts₀
  ...| no  _
    with pathFromRootM blockIdToCommit {state₀} {acts₀}
  ...| nothing , state₁ , acts₁ = [] , state₁ , acts₁
  ...| just blocksToCommit , state₁ , acts₁
    with pruneTreeM (ebId blockToCommit) {state₁} {acts₁}
  ...|  _ , state₂ , acts₂ = blocksToCommit , state₂ , acts₂
