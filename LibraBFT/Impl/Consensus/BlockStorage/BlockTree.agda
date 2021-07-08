{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Base.ByteString
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
  insertBlockE : ∀ {𝓔 : EpochConfig}
               → ExecutedBlock → BlockTree 𝓔
               → Either ErrLog (BlockTree 𝓔 × ExecutedBlock)

------------------------------------------------------------------------------

pathFromRoot : ∀ {𝓔 : EpochConfig}
             → HashValue → BlockTree  𝓔
             → Either ErrLog (List ExecutedBlock)
pathFromRoot blockId blockTree =
  maybeS (blockTree ^∙ btRoot _) (Left fakeErr) $ λ btr → {!!}
  -- maybeS (loop btr blockId []) (Right []) (pure ∘ continue)
 where
  loop : ExecutedBlock → HashValue → List ExecutedBlock → Maybe (HashValue × List ExecutedBlock)
  loop = {!!}
  -- loop btr curBlockId res = case btGetBlock _ curBlockId blockTree of λ where
  --   (just block) → if-dec (block ^∙ ebRound) ≤?ℕ (btr ^∙ ebRound)
  --                    then just (curBlockId , res)
  --                    else loop btr (block ^∙ ebParentId) (block ∷ res)
  --   nothing      → nothing
  continue : (HashValue × List ExecutedBlock) → List ExecutedBlock
  continue (curBlockId , res) = {!!}
    -- if curBlockId /= (blockTree ^∙ btRootId)
    -- then []
    -- else res
