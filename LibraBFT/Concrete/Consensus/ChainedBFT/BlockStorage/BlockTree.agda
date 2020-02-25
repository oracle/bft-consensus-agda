open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep
open import LibraBFT.Concrete.Consensus.Types.EventProcessor
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.Util.KVMap
open import LibraBFT.Concrete.OBM.Util
open import LibraBFT.Hash

open import Optics.All

module LibraBFT.Concrete.Consensus.ChainedBFT.BlockStorage.BlockTree
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
  open import LibraBFT.Concrete.BlockTree hash hash-cr


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

insertBlock :: ExecutedBlock a -> BlockTree a -> Either (ErrLog a) (BlockTree a)
insertBlock eb bt = do
  case btGetBlock (eb^.ebId) bt of
    Just b  -> Left (ErrExistingBlock       ["BlockTree", "insertBlock"] b (eb^.ebId) eb)
    Nothing -> pure ()
  case btGetLinkableBlock (eb^.ebParentId) bt of
    Nothing -> Left (ErrParentBlockNotFound ["BlockTree", "insertBlock"] (eb^.ebParentId))
    Just _  -> pure ()
  pure (bt & btIdToBlock .~ Map.insert (eb^.ebId) (linkableBlockNew eb) (bt^.btIdToBlock))

--}

  -- MSM: This is a first cut at modeling the Haskell code (see above).  Hopefully be made to look
  -- more obviously equivalent, but there are some ways in which it won't, for example because we
  -- cannot use lenses with dependent types (e.g., lBlockTree cannot be defined because there is no
  -- way to prove that the new value is for the same EpochConfig, AFAICT.

  insertBlock : ∀ {ec : Meta EpochConfig} → ExecutedBlock -> BlockTree {ec} -> Unit ⊎ BlockTree {ec}
  insertBlock {ec} eb bt with (lookup (_bId (_ebBlock eb))) (_btIdToBlock bt) |
                 inspect (lookup (_bId (_ebBlock eb))) (_btIdToBlock bt)
  ...| just _  | _ = inj₁ unit
  -- TODO: Here, we insert the block into the tree, so we need to provide an Extends.  This will
  -- come from properties we gather along the way.  idAvail is part of it, but other info needed,
  -- such as correct round, etc. will need to be carried along to here.
  ...| nothing | [ idAvail ] = inj₂ (insert-block ec bt (LinkableBlock_new eb) {!!})

  -- TODO: move to proper place and give proper name
  btLens : ∀ {ec : Meta EpochConfig} → Lens (BlockStore {ec}) (BlockTree {ec})
  btLens = mkLens' :bsInner
                   λ bs bt → record bs {:bsInner = bt}

  insertBlockM : ExecutedBlock → LBFT (Maybe ExecutedBlock)
  insertBlockM eb = do
    ep ← get
    continue ep eb  -- MSM: I needed to do this to use "with" after "do".  Can I avoid this?
    where
       continue : ∀ (ep : EventProcessor) → ExecutedBlock → LBFT (Maybe ExecutedBlock)
       continue ep eb with insertBlock eb ((:bsInner ∘ :epBlockStore) ep)  -- TODO: define/use lens
       ...| inj₁ e   = return nothing
       ...| inj₂ bt' = do
              put (record ep {:epBlockStore = set (:epBlockStore ep) btLens bt'})
              pure (just eb)

  -- TODO: logging
  -- TODO: Either vs ⊎

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
    -- However, because of dependent types, we cannot have such lenses (see comments in
    -- LibraBFT.Concrete.Consensus.Types.EventProcessor)
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
