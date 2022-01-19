{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.ByteString
open import Util.Hash
import      Util.KVMap                                           as Map
open import Util.PKCS
open import Util.Prelude
------------------------------------------------------------------------------
open import Data.String                                          using (String)

module LibraBFT.Impl.Consensus.BlockStorage.BlockTree where

postulate -- TODO-2: implement linkableBlockNew
  linkableBlockNew : ExecutedBlock → LinkableBlock

module addChild (lb : LinkableBlock) (hv : HashValue) where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog LinkableBlock

  postulate -- TODO-2: implement addChild
    step₀ : VariantFor EitherD
    -- addChild : LinkableBlock → HashValue → Either ErrLog LinkableBlock
    -- addChild lb hv =
    --   if Set.member hv (lb ^∙ lbChildren)
    --   then Left  fakeErr
    --   else Right (lb & lbChildren %~ Set.insert hv)

  E : VariantFor Either
  E = toEither step₀

abstract
  addChild   = addChild.step₀
  addChild-E = addChild.E

  addChild-≡ : addChild ≡ addChild.step₀
  addChild-≡ = refl

  addChild-≡-E : addChild-E ≡ addChild.E
  addChild-≡-E = refl

  addChild-≡-E1 : ∀ (lb : LinkableBlock) (hv : HashValue) → addChild-E lb hv ≡ EitherD-run (addChild lb hv)
  addChild-≡-E1 lb hv = refl

new : ExecutedBlock → QuorumCert → QuorumCert → Usize → Maybe TimeoutCertificate
    → Either ErrLog BlockTree
new root0 rootQuorumCert rootLedgerInfo maxPruned mHighestTimeoutCert = do
  lcheck ((root0 ^∙ ebId) == (rootLedgerInfo ^∙ qcCommitInfo ∙ biId))
         ("BlockTree" ∷ "newBlockTree" ∷ "inconsistent root and ledger info" ∷ [])
  let idToBlock      = Map.insert (root0 ^∙ ebId) (linkableBlockNew root0) Map.empty
      idToQuorumCert = Map.insert (rootQuorumCert ^∙ qcCertifiedBlock ∙ biId) rootQuorumCert Map.empty
      prunedBlockIds = vdNew -- TODO
   in pure $ mkBlockTree
    idToBlock
    (root0 ^∙ ebId)     -- _btRootId
    (root0 ^∙ ebId)     -- _btHighestCertifiedBlockId
    rootQuorumCert      -- _btHighestQuorumCert
    mHighestTimeoutCert
    rootLedgerInfo      -- _btHighestCommitCert
    idToQuorumCert
    prunedBlockIds
    maxPruned


replaceTimeoutCertM : TimeoutCertificate → LBFT Unit
replaceTimeoutCertM tc = do
  lBlockStore ∙ bsInner ∙ btHighestTimeoutCert ?= tc
  logInfo fakeInfo -- lTO (InfoUpdateHighestTimeoutCert (Just tc))

------------------------------------------------------------------------------

module insertBlockE (block : ExecutedBlock)(bt : BlockTree) where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog (BlockTree × ExecutedBlock)

  step₀ : VariantFor EitherD
  step₁ : HashValue → VariantFor EitherD
  step₂ : HashValue → LinkableBlock → VariantFor EitherD

  step₀ = do
    let blockId = block ^∙ ebId
    caseMD btGetBlock blockId bt of λ where
      (just existingBlock) → pure (bt , existingBlock)
      nothing → step₁ blockId

  step₁ blockId = do
      caseMD btGetLinkableBlock (block ^∙ ebParentId) bt of λ where
        nothing → LeftD fakeErr
        (just parentBlock) → step₂ blockId parentBlock

  step₂ blockId parentBlock = do
          parentBlock' ← addChild parentBlock blockId
          let bt' = bt & btIdToBlock ∙~ Map.kvm-insert-Haskell (block ^∙ ebParentId) parentBlock' (bt ^∙ btIdToBlock)
          pure (  (bt' & btIdToBlock ∙~ Map.kvm-insert-Haskell blockId (LinkableBlock∙new block) (bt' ^∙ btIdToBlock))
               , block)

--  E : VariantFor Either
--  E = toEither step₀

-- We make the EitherD variant the default, because the only call in code
-- modeled is in EitherD, so it's nice to keep it exactly like the Haskell
-- code being modeled.  However, insertBlockESpec.Contract and the proof of
-- executeAndInsertBlockESpec.contract' (which was written before EitherD
-- support was developed) both want an Either variant, so they use
-- insertBlockE.E.

-- When proving contracts about a function that is in Either, we would like the code to be in
-- EitherD, so we can take advantage of the EitherD structure.  However, when we want to say
-- something about the return value...
-- what about pattern matching?  Am I correct
-- EitherD-Post is defined in terms of Either, so we need contracts to be in terms of Either.
-- The E version provides that so we can reason about it, and relate the D version to it easily



-- This demonstrates the flexibility of the VariantOf
-- approach, providing variants for any EitherLike, and means to convert
-- between them easily.
abstract
  insertBlockE   = insertBlockE.step₀

  insertBlockE-≡ : insertBlockE ≡ insertBlockE.step₀
  insertBlockE-≡ = refl

insertBlockE-original : ExecutedBlock → BlockTree → Either ErrLog (BlockTree × ExecutedBlock)
insertBlockE-original block bt = do
  let blockId = block ^∙ ebId
  case btGetBlock blockId bt of λ where
    (just existingBlock) → pure (bt , existingBlock)
    nothing → case btGetLinkableBlock (block ^∙ ebParentId) bt of λ where
      nothing → Left fakeErr
      (just parentBlock) → (do
        parentBlock' ← addChild-E parentBlock blockId
        let bt' = bt & btIdToBlock ∙~ Map.kvm-insert-Haskell (block ^∙ ebParentId) parentBlock' (bt ^∙ btIdToBlock)
        pure (  (bt' & btIdToBlock ∙~ Map.kvm-insert-Haskell blockId (LinkableBlock∙new block) (bt' ^∙ btIdToBlock))
             , block))

insertBlockE-original-≡ : ∀ {block bt}
                          → insertBlockE-original block bt ≡ EitherD-run (insertBlockE block bt)
insertBlockE-original-≡ {block} {bt} rewrite insertBlockE-≡
   with btGetBlock (block ^∙ ebId) bt
... | just _  = refl
... | nothing
   with  btGetLinkableBlock (block ^∙ ebParentId) bt
... | nothing = refl
... | just parentBlock rewrite addChild-≡-E1 parentBlock (block ^∙ ebId)
   with EitherD-run (addChild parentBlock (block ^∙ ebId)) -- addChild.E parentBlock (block ^∙ ebId)
... | Left  x = refl
... | Right y = refl

------------------------------------------------------------------------------

module insertQuorumCertE (qc : QuorumCert) (bt0 : BlockTree) where

  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog (BlockTree × List InfoLog)

  step₁     : HashValue → VariantFor EitherD
  step₂     : HashValue → ExecutedBlock → VariantFor EitherD
  step₃     : HashValue → ExecutedBlock → ExecutedBlock → VariantFor EitherD
  continue1 : BlockTree → HashValue → ExecutedBlock → List InfoLog → (BlockTree × List InfoLog)
  continue2 : BlockTree → List InfoLog → (BlockTree × List InfoLog)
  here' : List String → List String
  here' t = "BlockTree" ∷ "insertQuorumCert" ∷ t

  blockId = qc ^∙ qcCertifiedBlock ∙ biId

  safetyInvariant = forM_ (Map.elems (bt0 ^∙ btIdToQuorumCert)) $ \x →
          lcheck (   (x  ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash
                  ==  qc ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash)
                  ∨  (x  ^∙ qcCertifiedBlock ∙ biRound
                  /=  qc ^∙ qcCertifiedBlock ∙ biRound))
                 (here' ("failed check" ∷ "existing qc == qc || existing qc.round /= qc.round" ∷ []))
  step₀ =
    case safetyInvariant of λ where
      (Left  e)    → LeftD e
      (Right unit) → step₁ blockId

  step₁ blockId =
        maybeSD (btGetBlock blockId bt0) (LeftD fakeErr) $ step₂ blockId 

  step₂ blockId block =
        maybeSD (bt0 ^∙ btHighestCertifiedBlock) (LeftD fakeErr) $ step₃ blockId block

  step₃ blockId block hcb =
        ifD ((block ^∙ ebRound) >? (hcb ^∙ ebRound))
        then
         (let bt   = bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId
                         & btHighestQuorumCert       ∙~ qc
              info = (fakeInfo ∷ [])
           in pure (continue1 bt  blockId block info))
        else  pure (continue1 bt0 blockId block [])

  continue1 bt blockId block info =
    continue2 ( bt & btIdToQuorumCert ∙~ lookupOrInsert blockId qc (bt ^∙ btIdToQuorumCert))
              ( (fakeInfo ∷ info) ++ (if ExecutedBlock.isNilBlock block then fakeInfo ∷ [] else [] ))

  continue2 bt info =
    if-dec (bt ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
    then ((bt & btHighestCommitCert ∙~ qc) , info)
    else (bt , info)

  E : VariantFor Either
  E = toEither step₀

  D : VariantFor EitherD
  D = fromEither E

insertQuorumCertE = insertQuorumCertE.E

insertQuorumCertM : QuorumCert → LBFT Unit
insertQuorumCertM qc = do
  bt ← use lBlockTree
  case insertQuorumCertE qc bt of λ where
    (Left  e)   → logErr e
    (Right (bt' , info)) → do
      forM_ info logInfo
      lBlockTree ∙= bt'

------------------------------------------------------------------------------

module pathFromRoot (blockId : HashValue) (blockTree : BlockTree) where

  -- TODO-1 PROVE IT TERMINATES
  {-# TERMINATING #-}
  loop : ExecutedBlock → HashValue → List ExecutedBlock → Maybe (HashValue × List ExecutedBlock)
  loop btr curBlockId res = case btGetBlock curBlockId blockTree of λ where
    (just block) → if-dec (block ^∙ ebRound) ≤?ℕ (btr ^∙ ebRound)
                     then just (curBlockId , res)
                     else loop btr (block ^∙ ebParentId) (block ∷ res)
    nothing      → nothing

pathFromRoot : HashValue → BlockTree → Either ErrLog (List ExecutedBlock)
pathFromRoot blockId blockTree =
  maybeS (blockTree ^∙ btRoot) (Left fakeErr) $ λ btr →
  maybeS (loop btr blockId []) (pure []) (pure ∘ continue)
 where

  open pathFromRoot blockId blockTree

  continue : (HashValue × List ExecutedBlock) → List ExecutedBlock
  continue (curBlockId , res) =
    if not (curBlockId /= (blockTree ^∙ btRootId))
    then []
    else res

------------------------------------------------------------------------------

getAllBlockIdM : LBFT (List HashValue)
getAllBlockIdM = Map.kvm-keys <$> use (lBlockTree ∙ btIdToBlock)
