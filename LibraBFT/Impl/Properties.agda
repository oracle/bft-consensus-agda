{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Concrete.System.Parameters

-- This module collects the implementation obligations for our (fake/simple, for now)
-- "implementation" into the structure required by Concrete.Properties.
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Impl.Handle.Properties
import      LibraBFT.Impl.Properties.VotesOnce   as VO
import      LibraBFT.Impl.Properties.PreferredRound as PR
open import LibraBFT.Concrete.Obligations
open import LibraBFT.Concrete.System

module LibraBFT.Impl.Properties (𝓔 : EpochConfig) where
  theImplObligations : ImplObligations 𝓔
  theImplObligations = record { sps-cor = impl-sps-avp
                              ; vo₁     = VO.vo₁ 𝓔
                              ; vo₂     = VO.vo₂ 𝓔
                              ; pr₁     = PR.pr₁ 𝓔
                              ; pr₂     = PR.pr₂ 𝓔
                              }
