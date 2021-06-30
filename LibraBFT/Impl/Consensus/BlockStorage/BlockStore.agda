{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

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

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

postulate
  executeAndInsertBlockM : Block → LBFT (Either FakeErr ExecutedBlock)
  insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either FakeErr Unit)
  getBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe ExecutedBlock
  getQuorumCertForBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe QuorumCert
  syncInfoM : LBFT SyncInfo
