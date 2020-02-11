open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.OBM.Util
open import LibraBFT.Hash

module LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree where

{--

pathFromRootM
  :: (Monad m, RWBlockTree s a)
  => HashValue
  -> LBFT m e s a (Maybe [ExecutedBlock a])
pathFromRootM blockId = do
  bt <- use lBlockTree
  maybeMP (loop bt blockId []) Nothing (continue bt)
 where
  loop bt curBlockId res = case btGetBlock curBlockId bt of
    Just block | block^.ebRound <= bt^.btRoot.ebRound -> pure (Just (curBlockId, res))
    Just block                                        -> loop bt (block^.ebParentId) (block : res)
    Nothing                                           -> pure Nothing
  continue bt (curBlockId, res) =
    if curBlockId /= bt^.btRootId
    then pure Nothing
    else pure (Just (reverse res))

--}

  {-# TERMINATING #-}  -- TODO: justify or eliminate
  pathFromRootM : HashValue → LBFT (Maybe (List (ExecutedBlock TX)))
  pathFromRootM blockId {state₀}
    with use lBlockTree {state₀}
  ...| bt = maybeMP (loop bt blockId [] {state₀}) nothing (continue bt) {state₀}
       where
         loop : BlockTree TX → HashValue → List (ExecutedBlock TX) → LBFT (Maybe (HashValue × List (ExecutedBlock TX)))
         loop bt curBlockId res {state₀}
            with btGetBlock curBlockId bt
         ...| nothing = nothing , state₀ , []
         ...| just block
            with ebRound block ≤? (ebRound ∘ btRoot) bt
         ...| yes xx = just (curBlockId , res) , state₀ , []
         ...| no  xx = loop bt (ebParentId block) (block ∷ res) {state₀}

         continue : {a : Set} → BlockTree a → HashValue × List (ExecutedBlock TX) → LBFT (Maybe (List (ExecutedBlock TX)))
         continue bt (curBlockId , res) {state₀}
           with curBlockId ≟Hash btRootId bt
         ...| no _  = nothing            , state₀ , []
         ...| yes _ = just (reverse res) , state₀ , []
