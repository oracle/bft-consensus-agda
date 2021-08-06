{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Prelude
open import Optics.All

open RoundManagerInvariants
open QCProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree where


module insertQuorumCertESpec
  (qc : QuorumCert) (bt0  : BlockTree) where

  Contract : Either ErrLog (BlockTree × List InfoLog) → Set
  Contract (Left _) = Unit
  Contract (Right (bt1 , il)) = ∀ {qc'} → qc' ∈BlockTree bt1 → qc' ∈BlockTree bt0 ⊎ qc' ≡ qc

  postulate -- TODO-1: prove it
    contract : Contract (insertQuorumCertE qc bt0)
