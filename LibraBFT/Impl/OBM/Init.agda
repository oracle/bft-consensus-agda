{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.Liveness.RoundState              as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ExponentialTimeInterval as ExponentialTimeInterval
import      LibraBFT.Impl.OBM.ConfigHardCoded                        as ConfigHardCoded
open import LibraBFT.Impl.OBM.Rust.Duration                          as Duration
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Time
open import LibraBFT.ImplShared.Consensus.Types

module LibraBFT.Impl.OBM.Init where

------------------------------------------------------------------------------

-- TODO : get numbers from config

dT : Duration
dT = Duration.fromMillis ConfigHardCoded.roundInitialTimeoutMS

etiT : ExponentialTimeInterval
etiT = ExponentialTimeInterval.new dT 2 {-1.2-} 6 -- TODO FLOAT

rsT : RoundState
rsT = RoundState.new etiT timeT
