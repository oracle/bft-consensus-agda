{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore (𝓔 : EpochConfig) where
-- TODO-1: Implement this
postulate
  getBlock : HashValue → BlockStore 𝓔 → Maybe ExecutedBlock


