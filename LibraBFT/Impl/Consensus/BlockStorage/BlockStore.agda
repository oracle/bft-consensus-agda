{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where
-- TODO-1: Implement these.
postulate
  executeAndInsertBlockM : Block → LBFT (Unit ⊎ ExecutedBlock)
  getBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe ExecutedBlock
  getQuorumCertForBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe QuorumCert
  syncInfo : LBFT SyncInfo

{-
executeAndInsertBlockM
  :: (Monad m, Show a, RWBlockStore s a)
  => Block a
  -> LBFT m e s a (Either (ErrLog a) (ExecutedBlock a))
-}
