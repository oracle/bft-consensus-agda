open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep
open import LibraBFT.Concrete.Consensus.Types.EventProcessor
open import LibraBFT.Concrete.Records
import      LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree as BlockTree
open import LibraBFT.Hash

open import Optics.All

open import LibraBFT.Concrete.OBM.Util

module LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockStore
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  getBlock : ∀ {ec : Meta EpochConfig} → HashValue -> BlockStore {ec} -> Maybe ExecutedBlock
  getBlock hv bs = btGetBlock hv (bs ^∙ bsInner)

  open RWST-do

  pathFromRootM : HashValue → LBFT (Maybe (List ExecutedBlock))
  pathFromRootM = BlockTree.pathFromRootM

  pruneTreeM : HashValue -> LBFT Unit
  pruneTreeM _ = return unit
    -- TODO prune
    -- BlockTree.processPrunedBlocksM

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

  commitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
  commitM finalityProof = do
    -- We cannot do "bs <- use lBlockStore" as in Haskell code.  See comments in
    -- BlockTree.agda about why we use the following instead.
    ep ← get
    let bs = :epBlockStore ep

        blockIdToCommit = finalityProof ^∙ liwsLedgerInfo ∙ liConsensusBlockId
    case getBlock blockIdToCommit bs of
      λ { nothing              → pure [] 
        ; (just blockToCommit) →
            -- MSM: Any chance of some more syntactic sugar so we can be closer
            -- to the guards syntax used in Haskell (see above)?
            if-dec (blockToCommit ^∙ ebRound ≤? (bsRoot bs) ^∙ ebRound)
            then tell1 (LogErr "commit block round lower than root") >> pure []
            else do 
             blocksToCommit ← maybe id [] <$> pathFromRootM blockIdToCommit 
             pruneTreeM (blockToCommit ^∙ ebId)
             pure blocksToCommit
        }
{-
OLD:

  commitM finalityProof {state₀} {acts₀}
    with use lBlockStore {state₀}
  ...| bs
    with (liConsensusBlockId ∘ liwsLedgerInfo) finalityProof
  ...| blockIdToCommit
    with getBlock blockIdToCommit bs
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
