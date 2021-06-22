{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}


open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Logging.Logging where

  open RWST-do

  logErr : LBFT Unit
  logErr = tell1 (LogErr fakeErr)

  logInfo : LBFT Unit
  logInfo = tell1 (LogInfo fakeInfo)
