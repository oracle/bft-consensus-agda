{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.BlockInfo where


gENESIS_EPOCH   : Epoch
gENESIS_EPOCH   = {-Epoch-} 0

gENESIS_ROUND   : Round
gENESIS_ROUND   = {-Round-} 0

gENESIS_VERSION : Version
gENESIS_VERSION = Version∙new 0 0

empty : BlockInfo
empty = BlockInfo∙new
  gENESIS_EPOCH
  gENESIS_ROUND
  (sha256 (false ∷ [])) -- TODO-1 Hash.valueZero
  (sha256 (false ∷ [])) -- TODO-1 Hash.valueZero
  gENESIS_VERSION
  nothing

hasReconfiguration : BlockInfo → Bool
hasReconfiguration = is-just ∘ (_^∙ biNextEpochState)
