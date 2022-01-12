{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Rust.Duration     as Duration
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.Prelude

module LibraBFT.Impl.Consensus.Liveness.ExponentialTimeInterval where

new : Duration → F64 → Usize → ExponentialTimeInterval
new base exponentBase maxExponent =
{- TODO-1
  if | maxExponent >= 32
       -> errorExit [ "ExponentialTimeInterval", "new"
                    , "maxExponent for PacemakerTimeInterval should be < 32", show maxExponent ]
     | ceiling (exponentBase ** fromIntegral maxExponent) >= {-F64-} (maxBound::Int)
       -> errorExit [ "ExponentialTimeInterval", "new"
                    , "maximum interval multiplier should be less then u32::Max"]
     | otherwise
       ->
-}        mkExponentialTimeInterval
            (Duration.asMillis base)
            exponentBase
            maxExponent
