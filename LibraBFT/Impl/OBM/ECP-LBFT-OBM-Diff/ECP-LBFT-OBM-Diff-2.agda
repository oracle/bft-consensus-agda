{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-0 as ECP-LBFT-OBM-Diff-0
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Storage.DiemDB.DiemDB                     as DiemDB
import      LibraBFT.Impl.Types.EpochChangeProof                    as EpochChangeProof
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-2 where

-- This is a separate file to avoid a cyclic dependency.

------------------------------------------------------------------------------

e_DiemDB_getEpochEndingLedgerInfosImpl_limit : Epoch → Epoch → Epoch → (Epoch × Bool)
e_DiemDB_getEpochEndingLedgerInfosImpl_limit startEpoch endEpoch limit =
  if not ECP-LBFT-OBM-Diff-0.enabled
  then
    if-dec endEpoch >? startEpoch + limit
    then (startEpoch + limit , true)
    else (endEpoch           , false)
  else   (endEpoch           , false)
