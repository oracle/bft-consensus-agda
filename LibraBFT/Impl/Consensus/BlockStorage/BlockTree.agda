{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap                         as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.BlockTree where

postulate
  addChild : LinkableBlock → HashValue → Either ErrLog LinkableBlock

  insertQuorumCertE
    : ∀ {𝓔 : EpochConfig}
    → QuorumCert → BlockTree 𝓔
    → Either ErrLog (BlockTree 𝓔)

------------------------------------------------------------------------------

-- addChild : LinkableBlock → HashValue → Either ErrLog LinkableBlock
-- addChild lb hv =
--   if Set.member hv (lb ^∙ lbChildren)
--   then Left  fakeErr
--   else Right (lb & lbChildren %~ Set.insert hv)

------------------------------------------------------------------------------

insertBlockE : ExecutedBlock → BlockTree
               → Either ErrLog (BlockTree × ExecutedBlock)
insertBlockE block bt = do
  let blockId = block ^∙ ebId
  case btGetBlock blockId bt of λ where
    (just existingBlock) → pure (bt , existingBlock)
    nothing → case btGetLinkableBlock (block ^∙ ebParentId) bt of λ where
      nothing → Left fakeErr
      (just parentBlock) → (do
        parentBlock' ← addChild parentBlock blockId
        let bt'  = bt & btIdToBlock ∙~ Map.insert (block ^∙ ebParentId) parentBlock' (bt ^∙ btIdToBlock)
        pure ( (bt' & btIdToBlock ∙~ Map.insert blockId (LinkableBlock∙new block) (bt' ^∙ btIdToBlock))
             , block))

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
  maybeS (loop btr blockId []) (Right []) (pure ∘ continue)
 where

  open pathFromRoot blockId blockTree

  continue : (HashValue × List ExecutedBlock) → List ExecutedBlock
  continue (curBlockId , res) =
    if not (curBlockId /= (blockTree ^∙ btRootId))
    then []
    else res
