{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Data.String using (String)
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude
open import Optics.All

{- Defines meta-level instrumentation for epoch-independent types in order to
-- reason about the implementation.
-}
module LibraBFT.ImplShared.Consensus.Types.MetaEpochIndep where
