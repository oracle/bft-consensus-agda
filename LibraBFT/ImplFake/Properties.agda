{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Concrete.Obligations
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.ImplFake.Handle
open import LibraBFT.ImplFake.Handle.Properties
import      LibraBFT.ImplFake.Properties.VotesOnce      as Common
import      LibraBFT.ImplFake.Properties.VotesOnce      as VO
import      LibraBFT.ImplFake.Properties.PreferredRound as PR
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

-- This module collects the implementation obligations for our (fake/simple, for now)
-- "implementation" into the structure required by Concrete.Properties.

module LibraBFT.ImplFake.Properties (𝓔 : EpochConfig) where
  theImplObligations : ImplObligations FakeInitAndHandlers 𝓔
  theImplObligations = record { sps-cor = impl-sps-avp
                              ; gvc     = genVotesConsistent
                              ; gvr     = genVotesRound≡0
                              ; v≢0     = ¬genVotesRound≢0
                              ; ∈GI?    = ∈GenInfo?-impl genesisInfo
                              ; iro     = Common.vo₁ 𝓔
                              ; vo₂     = VO.vo₂ 𝓔
                              ; pr₁     = PR.pr₁ 𝓔
                              ; pr₂     = PR.pr₂ 𝓔
                              }
