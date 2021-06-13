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

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

open RWST-do

module ExecuteAndInsertBlockM (b : Block) where
  postulate
    contract-rwst-∙?∙
      : ∀ {A} P pre (m : ExecutedBlock → LBFT (ErrLog ⊎ A))
        → P (inj₁ unit) pre []
        → (∀ eb blockStore → RWST-weakestPre (m eb) P unit (rmSetBlockStore pre blockStore))
        → RWST-weakestPre (executeAndInsertBlockM b ∙?∙ m) P unit pre
