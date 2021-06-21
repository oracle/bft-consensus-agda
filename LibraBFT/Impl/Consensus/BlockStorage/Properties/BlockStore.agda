{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

open RWST-do

module ExecuteAndInsertBlockM (b : Block) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ fakeErr) pre []
        → (∀ eb blockStore → P (inj₂ eb) (rmSetBlockStore pre blockStore) [])
        → RWST-weakestPre (executeAndInsertBlockM b) P unit pre

module syncInfoMSpec where
  postulate
    contract
      : ∀ P pre
        → (∀ si → P si pre [])
        → RWST-weakestPre syncInfoM P unit pre
