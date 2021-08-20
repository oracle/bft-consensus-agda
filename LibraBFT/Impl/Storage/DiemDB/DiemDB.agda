{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                            as String

open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD.Syntax

module LibraBFT.Impl.Storage.DiemDB.DiemDB where

module getEpochEndingLedgerInfos where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL =
    DiemDB → Epoch → Epoch
    → EL ErrLog (List LedgerInfoWithSignatures × Bool)

  postulate
    step₀ : VariantFor EitherD

  E : VariantFor Either
  E db ep = toEither ∘ step₀ db ep

  D : VariantFor EitherD
  D db ep = fromEither ∘ E db ep

getEpochEndingLedgerInfos = getEpochEndingLedgerInfos.E

module saveTransactions where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL =
    DiemDB {- → [TransactionToCommit] → Version-} → Maybe LedgerInfoWithSignatures
    → EL ErrLog DiemDB

  postulate
    step₀ : VariantFor EitherD

  E : VariantFor Either
  E db = toEither ∘ step₀ db

  D : VariantFor EitherD
  D db = fromEither ∘ E db

saveTransactions = saveTransactions.D



