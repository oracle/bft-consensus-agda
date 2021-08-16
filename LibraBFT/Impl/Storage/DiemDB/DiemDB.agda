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

module LibraBFT.Impl.Storage.DiemDB.DiemDB where

postulate
  getEpochEndingLedgerInfos
    : DiemDB → Epoch → Epoch
    → Either ErrLog (List LedgerInfoWithSignatures × Bool)
  saveTransactions
    : DiemDB {- → [TransactionToCommit] → Version-} → Maybe LedgerInfoWithSignatures
    → Either ErrLog DiemDB



