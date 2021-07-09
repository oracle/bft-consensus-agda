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

------------------------------------------------------------------------------

-- addChild : LinkableBlock → HashValue → Either ErrLog LinkableBlock
-- addChild lb hv =
--   if Set.member hv (lb ^∙ lbChildren)
--   then Left  fakeErr
--   else Right (lb & lbChildren %~ Set.insert hv)

------------------------------------------------------------------------------

insertBlockE : ∀ {𝓔 : EpochConfig}
             → ExecutedBlock → BlockTree 𝓔
             → Either ErrLog (BlockTree 𝓔 × ExecutedBlock)
insertBlockE block bt = do
  let blockId = block ^∙ ebId
  case btGetBlock _ blockId bt of λ where
    (just existingBlock) → pure (bt , existingBlock)
    nothing → case btGetLinkableBlock _ (block ^∙ ebParentId) bt of λ where
      nothing → Left fakeErr
      (just parentBlock) → (do
        parentBlock' ← addChild parentBlock blockId
        let bt'  = bt & btIdToBlock _ ∙~ Map.insert (block ^∙ ebParentId) parentBlock' (bt ^∙ btIdToBlock _)
        pure ( (bt' & btIdToBlock _ ∙~ Map.insert blockId (LinkableBlock∙new block) (bt' ^∙ btIdToBlock _))
             , block))

------------------------------------------------------------------------------

module pathFromRoot {𝓔 : EpochConfig} (blockId : HashValue) (blockTree : BlockTree 𝓔) where

  -- TODO-1 PROVE IT TERMINATES
  {-# TERMINATING #-}
  loop : ExecutedBlock → HashValue → List ExecutedBlock → Maybe (HashValue × List ExecutedBlock)
  loop btr curBlockId res = case btGetBlock _ curBlockId blockTree of λ where
    (just block) → if-dec (block ^∙ ebRound) ≤?ℕ (btr ^∙ ebRound)
                     then just (curBlockId , res)
                     else loop btr (block ^∙ ebParentId) (block ∷ res)
    nothing      → nothing

pathFromRoot : ∀ {𝓔 : EpochConfig}
             → HashValue → BlockTree  𝓔
             → Either ErrLog (List ExecutedBlock)
pathFromRoot blockId blockTree =
  maybeS (blockTree ^∙ btRoot _) (Left fakeErr) $ λ btr →
  maybeS (loop btr blockId []) (Right []) (pure ∘ continue)
 where

  open pathFromRoot blockId blockTree

  continue : (HashValue × List ExecutedBlock) → List ExecutedBlock
  continue (curBlockId , res) =
    if not (curBlockId /= (blockTree ^∙ btRootId _))
    then []
    else res
