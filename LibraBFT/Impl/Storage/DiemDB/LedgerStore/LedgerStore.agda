{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Base.KVMap                 as Map
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.Storage.DiemDB.LedgerStore.LedgerStore where

new : LedgerStore
new = mkLedgerStore Map.empty Map.empty nothing

record EpochEndingLedgerInfoIter : Set where
  constructor EpochEndingLedgerInfoIter∙new
  field
    _eeliiObmLIWS : List LedgerInfoWithSignatures
open EpochEndingLedgerInfoIter public

postulate
 getEpochEndingLedgerInfo     : LedgerStore → Version → Either ErrLog LedgerInfoWithSignatures
 getEpochEndingLedgerInfoIter : LedgerStore → Epoch → Epoch → Either ErrLog EpochEndingLedgerInfoIter
 putLedgerInfo                : LedgerStore → LedgerInfoWithSignatures → Either ErrLog LedgerStore

obmEELIICollect : EpochEndingLedgerInfoIter → List LedgerInfoWithSignatures
obmEELIICollect = _eeliiObmLIWS
