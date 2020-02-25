open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep
open import LibraBFT.Concrete.Consensus.Types.EventProcessor
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.OBM.Util
open import LibraBFT.Hash

open import Optics.All

module LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

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

  -- Bring in our RWST do notation into scope module wise;
  -- instead of over a single function as shown in LibraBFT.Concrete.OBM.RWST
  open RWST-do


{--

insertBlockM
  :: (Monad m, RWBlockTree s a)
  => ExecutedBlock a
  -> LBFT m e s a (Maybe (ExecutedBlock a))
insertBlockM eb = use lBlockTree >>= \bt -> case insertBlock eb bt of
  Left  e   -> do
    logErr e
    pure Nothing
  Right bt' -> do
    lBlockTree .= bt'   -- MSM: Note that the Haskell code uses lenses to modify the BlockTree, but we cannot
                        -- do that as we'll have to ...
    logInfo (InfoUpdateIdToBlockInsert eb)
    pure (Just eb)

--}

  -- VCM: This pathFromRootM function is exactly what our 'Extends' predicate
  -- will be doing as the boundary of concrete and abstract; The terminating
  -- can only be justified through that!
  --
  -- Ideally; 
  -- define: (extends? : ⋯ → Dec Extends) 
  -- then define: (getBlocks : Extends → List ExecutedBlock)
  -- then define: (agda-pathFromRootM = getBlocks ∘ extends?)
  -- finally; prove (∀ h → pathFromRootM h ≡ agda-pathFromRootM h);
  -- This should justify the terminating prama (which can't be eliminated;
  -- loop might in fact never terminate).
  --
  -- MSM: I don't think this is quite right, because Extends doesn't know anything about btRoot, so
  -- getBlocks would not be able to return only the blocks not yet committed. Maybe we need:
  -- (getBlocks : Extends → Round → List ExecutedBlock).  Otherwise, it seems to roughly make sense.

  {-# TERMINATING #-}  -- TODO: justify or eliminate
  pathFromRootM : HashValue → LBFT (Maybe (List ExecutedBlock))
  pathFromRootM blockId = do
    -- Haskell code is:
    --
    --   bt <- use lBlockTree
    --
    -- Note that lBlockTree is a GetterNoFunctor 
    --
    -- For now, use the following workaround.

    _ , bt ← gets (λ ep → :epEpochConfig ep , (:bsInner ∘ :epBlockStore) ep)

    maybeMP (loop bt blockId []) nothing (continue bt)
   where
    -- VCM: Both loop and continue are pure functions; why are
    -- they inside the LBFT monad? this will be more difficult
    -- to prove isomorphic to agda-pathFromRootM as described
    -- in my comment above.

    loop : {ec : Meta EpochConfig} → BlockTree {ec} → HashValue → List ExecutedBlock
         → LBFT (Maybe (HashValue × List ExecutedBlock))
    loop {ec} bt curBlockId res =
      case btGetBlock curBlockId bt of
        λ { nothing      → return nothing
          ; (just block) → if-dec (block ^∙ ebRound  ≤? (btRoot bt) ^∙ ebRound)
                            then return (just (curBlockId , res))
                            else loop bt (block ^∙ ebParentId) (block ∷ res)
          }

    continue : {ec : Meta EpochConfig} → BlockTree {ec} → HashValue × List ExecutedBlock
             → LBFT (Maybe (List ExecutedBlock))
    continue {ec} bt (curBlockId , res) =
      if-dec (curBlockId ≟Hash (bt ^∙ btRootId))
       then return (just (reverse res))
       else return nothing
    
{-
  OLD FUNCTION:
  
  pathFromRootM blockId {state₀} {acts₀}
    with use lBlockTree {state₀}
  ...| bt = maybeMP (loop bt blockId [] {state₀} {acts₀}) nothing (continue bt) {state₀} {acts₀}
       where
         loop : BlockTree → HashValue → List ExecutedBlock → LBFT (Maybe (HashValue × List ExecutedBlock))
         loop bt curBlockId res {state₀} {acts₀}
            with btGetBlock curBlockId bt
         ...| nothing = nothing , state₀ , acts₀
         ...| just block
            with ebRound block ≤? (ebRound ∘ btRoot) bt
         ...| yes xx = just (curBlockId , res) , state₀ , acts₀
         ...| no  xx = loop bt (ebParentId block) (block ∷ res) {state₀} {acts₀}

         continue : BlockTree → HashValue × List ExecutedBlock → LBFT (Maybe (List ExecutedBlock))
         continue bt (curBlockId , res) {state₀} {acts₀}
           with curBlockId ≟Hash btRootId bt
         ...| no _  = nothing            , state₀ , acts₀
         ...| yes _ = just (reverse res) , state₀ , acts₀
-}
