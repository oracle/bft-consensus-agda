{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto           as Crypto
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.Ledger2WaypointConverter where

new : LedgerInfo → Ledger2WaypointConverter
new ledgerInfo = mkLedger2WaypointConverter
  (ledgerInfo ^∙ liEpoch)
  (ledgerInfo ^∙ liTransactionAccumulatorHash)
  (ledgerInfo ^∙ liVersion)
--(ledgerInfo ^∙ liTimestamp)
  (ledgerInfo ^∙ liNextEpochState)
