{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.System
open import LibraBFT.Impl.Consensus.Types

import      LibraBFT.Concrete.Properties.VotesOnce      as VO
import      LibraBFT.Concrete.Properties.PreferredRound as PR

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

-- This module collects in one place the obligations an
-- implementation must meet in order to enjoy the properties
-- proved in Abstract.Properties.

module LibraBFT.Concrete.Obligations (𝓔 : EpochConfig) where
  record ImplObligations : Set (ℓ+1 ℓ-RoundManager) where
    field
      -- Structural obligations:
      sps-cor : StepPeerState-AllValidParts

      -- Semantic obligations:
      --
      -- VotesOnce:
      vo₁ : VO.ImplObligation₁ 𝓔
      vo₂ : VO.ImplObligation₂ 𝓔

      -- PreferredRound:
      pr₁ : PR.ImplObligation₁ 𝓔
      pr₂ : PR.ImplObligation₂ 𝓔
