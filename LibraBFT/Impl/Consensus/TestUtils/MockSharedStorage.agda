{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                            as Map
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.RecoveryData           as RecoveryData
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.LedgerInfo                 as LedgerInfo
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                               as String

module LibraBFT.Impl.Consensus.TestUtils.MockSharedStorage where

new : ValidatorSet → MockSharedStorage
new = mkMockSharedStorage
  Map.empty
  Map.empty
  Map.empty
  nothing
  nothing

newObmWithLIWS : ValidatorSet → LedgerInfoWithSignatures → MockSharedStorage
newObmWithLIWS vs obmLIWS =
  new vs & mssLis ∙~ Map.singleton (obmLIWS ^∙ liwsVersion) obmLIWS
