{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.System
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base

-- This module collects in one place the obligations an
-- implementation must meet in order to enjoy the properties
-- proved in Abstract.Properties.


module LibraBFT.Concrete.Obligations (iiah : SystemInitAndHandlers ℓ-RoundManager ConcSysParms) (𝓔 : EpochConfig) where
  import      LibraBFT.Concrete.Properties.PreferredRound iiah as PR
  import      LibraBFT.Concrete.Properties.VotesOnce      iiah as VO
  import      LibraBFT.Concrete.Properties.Common         iiah as Common


  open        SystemTypeParameters ConcSysParms
  open        SystemInitAndHandlers iiah
  open        ParamsWithInitAndHandlers iiah
  open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms iiah
                                 PeerCanSignForPK PeerCanSignForPK-stable

  record ImplObligations : Set (ℓ+1 ℓ-RoundManager) where
    field
      -- Structural obligations:
      sps-cor : StepPeerState-AllValidParts

      -- Semantic obligations:
      --
      -- VotesOnce:
      gvc  : Common.ImplObl-genVotesConsistent 𝓔
      gvr  : Common.ImplObl-genVotesRound≡0 𝓔
      v≢0  : Common.ImplObl-NewVoteRound≢0 𝓔
      ∈GI? : (sig : Signature) → Dec (∈GenInfo genInfo sig)
      iro : Common.IncreasingRoundObligation 𝓔
      vo₂ : VO.ImplObligation₂ 𝓔

      -- PreferredRound:
      pr₁ : PR.ImplObligation₁ 𝓔
      pr₂ : PR.ImplObligation₂ 𝓔
