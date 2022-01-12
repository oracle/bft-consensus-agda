{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.Ledger2WaypointConverter as Ledger2WaypointConverter
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto              as Crypto
open import Optics.All
open import Util.Hash
open import Util.Prelude
open import Util.Types

module LibraBFT.Impl.Types.Waypoint where

newAny : LedgerInfo → Waypoint
newAny ledgerInfo =
  let converter = Ledger2WaypointConverter.new ledgerInfo
   in Waypoint∙new (ledgerInfo ^∙ liVersion) (Crypto.hashL2WC converter)

newEpochBoundary : LedgerInfo → Either ErrLog Waypoint
newEpochBoundary ledgerInfo =
  if ledgerInfo ^∙ liEndsEpoch
  then pure (newAny ledgerInfo)
  else Left fakeErr -- ["newEpochBoundary", "no validator set"]

verify : Waypoint → LedgerInfo → Either ErrLog Unit
verify self ledgerInfo = do
  lcheck (self ^∙ wVersion == ledgerInfo ^∙ liVersion)
         ("Waypoint" ∷ "version mismatch" ∷ []) --show (self^.wVersion), show (ledgerInfo^.liVersion)]
  let converter = Ledger2WaypointConverter.new ledgerInfo
  lcheck (self ^∙ wValue == Crypto.hashL2WC converter)
         ("Waypoint" ∷ "value mismatch" ∷ []) --show (self^.wValue), show (Crypto.hashL2WC converter)]
  pure unit

epochChangeVerificationRequired : Waypoint → Epoch → Bool
epochChangeVerificationRequired _self _epoch = true

isLedgerInfoStale : Waypoint → LedgerInfo → Bool
isLedgerInfoStale self ledgerInfo = ⌊ (ledgerInfo ^∙ liVersion) <?-Version (self ^∙ wVersion) ⌋

verifierVerify : Waypoint → LedgerInfoWithSignatures → Either ErrLog Unit
verifierVerify self liws = verify self (liws ^∙ liwsLedgerInfo)
