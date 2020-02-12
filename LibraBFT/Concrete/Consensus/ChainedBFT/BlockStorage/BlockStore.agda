open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Records
import      LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree as BlockTree


open import LibraBFT.Concrete.OBM.Util

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

  open RWST-do

  pathFromRootM : HashValue → LBFT (Maybe (List (ExecutedBlock TX)))
  pathFromRootM = BlockTree.pathFromRootM

  pruneTreeM : HashValue -> LBFT Unit
  pruneTreeM _ = return unit
    -- TODO prune
    -- BlockTree.processPrunedBlocksM

  commitM : LedgerInfoWithSignatures → LBFT (List (ExecutedBlock TX))
  commitM finalityProof = do
    bs ← gets lBlockStore
    let blockIdToCommit = (liConsensusBlockId ∘ liwsLedgerInfo) finalityProof
    case getBlock blockIdToCommit bs of
      λ { nothing              → return [] 
        ; (just blockToCommit) → 
            if-dec (ebRound blockToCommit ≤? ebRound (bsRoot bs))
            then tell1 (LogErr "commit block round lower than root") >> return []
            else do 
             blocksToCommit ← maybe id [] <$> pathFromRootM blockIdToCommit 
             pruneTreeM (ebId blockToCommit)
             return blocksToCommit
        }
{-
OLD:

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
-}
