{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.ConsensusProvider            as ConsensusProvider
open import LibraBFT.Impl.Consensus.Properties.ConsensusProvider as ConsensusProviderProps
import      LibraBFT.Impl.IO.OBM.GenKeyFile                      as GenKeyFile
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Start
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open Invariants
open RoundManagerTransProps
open InitProofDefs

module LibraBFT.Impl.IO.OBM.Properties.Start where

module startViaConsensusProviderSpec
  (now   : Instant)
  (nfl   : GenKeyFile.NfLiwsVsVvPe)
  (txTDS : TxTypeDependentStuffForNetwork)
  where
  -- It is somewhat of an overkill to write a separate contract for the last step,
  -- but keeping it explicit for pedagogical reasons
  contract-step₁ : ∀ (tup : (NodeConfig × OnChainConfigPayload × LedgerInfoWithSignatures × SK × ProposerElection))
                 → EitherD-weakestPre (startViaConsensusProvider-ed.step₁ now nfl txTDS tup) (InitContract nothing)
  contract-step₁ (nodeConfig , payload , liws , sk , pe) =
    startConsensusSpec.contract' nodeConfig now payload liws sk ObmNeedFetch∙new
                                 (txTDS ^∙ ttdsnProposalGenerator) (txTDS ^∙ ttdsnStateComputer)

  contract' : EitherD-weakestPre (startViaConsensusProvider-ed-abs now nfl txTDS) (InitContract nothing)
  contract' rewrite startViaConsensusProvider-ed-abs-≡ =
    -- TODO-2: this is silly; perhaps we should have an EitherD-⇒-bind-const or something for when
    -- we don't need to know anything about the values returned by part before the bind?
    EitherD-⇒-bind (ConsensusProvider.obmInitialData-ed-abs nfl)
                   (EitherD-vacuous (ConsensusProvider.obmInitialData-ed-abs nfl))
                   P⇒Q
       where
       P⇒Q : EitherD-Post-⇒ (const Unit) (EitherD-weakestPre-bindPost _ (InitContract nothing))
       P⇒Q (Left _)     _        = tt
       P⇒Q (Right tup') _ c refl = contract-step₁ tup'
