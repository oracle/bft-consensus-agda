{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.BlockData  as BlockData
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Types.BlockInfo                     as BlockInfo
import      LibraBFT.Impl.Types.ValidatorVerifier             as ValidatorVerifier
open import LibraBFT.Impl.OBM.Crypto hiding (verify)
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.PKCS                                         hiding (verify)
open import Util.Prelude
open import Util.Types
open import Util.Hash
------------------------------------------------------------------------------
open import Data.String                                       using (String)

module LibraBFT.Impl.Consensus.ConsensusTypes.BlockRetrieval where

verify : BlockRetrievalResponse → HashValue → U64 → ValidatorVerifier → Either ErrLog Unit
verify self blockId numBlocks sigVerifier =
  grd‖ self ^∙ brpStatus /= BRSSucceeded ≔
       Left fakeErr -- here ["/= BRSSucceeded"]
     ‖ length (self ^∙ brpBlocks) /= numBlocks ≔
       Left fakeErr -- here ["not enough blocks returned", show (self^.brpBlocks), show numBlocks]
     ‖ otherwise≔
       verifyBlocks (self ^∙ brpBlocks)
 where
  here' : List String → List String
  here' t = "BlockRetrieval" ∷ "verify" ∷ t

  verifyBlock : HashValue → Block → Either ErrLog HashValue

  verifyBlocks : List Block → Either ErrLog Unit
  verifyBlocks blks = foldM_ verifyBlock blockId blks

  verifyBlock expectedId block = do
    Block.validateSignature block sigVerifier
    Block.verifyWellFormed  block
    lcheck (block ^∙ bId == expectedId)
           (here' ("blocks do not form a chain" ∷ [])) -- lsHV (block^.bId), lsHV expectedId
    pure (block ^∙ bParentId)

