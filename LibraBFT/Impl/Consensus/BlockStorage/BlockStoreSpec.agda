{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore

module LibraBFT.Impl.Consensus.BlockStorage.BlockStoreSpec where

-- TODO-1: Prove these (once the related functions have been implemented)
module _ (b : Block) (rm : RoundManager) where
  postulate
    executeAndInsertBlockM-RW
      : let rm' = LBFT-post (executeAndInsertBlockM b) rm in ₋rmEC rm' ≡ ₋rmEC rm

    executeAndInsertBlockM-noOutput
      : let outs = LBFT-outs (executeAndInsertBlockM b) rm in outs ≡ []

module _ (rm : RoundManager) where
  postulate
    syncInfo-noOutput
      : let outs = LBFT-outs syncInfo rm in outs ≡ []
