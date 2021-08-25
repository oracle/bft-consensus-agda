{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.OnChainConfig.ValidatorSet where

new : List ValidatorInfo → ValidatorSet
new = ValidatorSet∙new ConsensusScheme∙new

empty : ValidatorSet
empty = new []

postulate -- TODO-1 obmFromVV
  obmFromVV : ValidatorVerifier → ValidatorSet
