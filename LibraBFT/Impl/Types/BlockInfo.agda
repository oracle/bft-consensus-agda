{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.Types.BlockInfo where

empty : BlockInfo
empty = BlockInfo∙new
  0                     -- TODO-1 gENESIS_EPOCH
  0                     -- TODO-1 gENESIS_ROUND
  (sha256 (false ∷ [])) -- TODO-1 Hash.valueZero

