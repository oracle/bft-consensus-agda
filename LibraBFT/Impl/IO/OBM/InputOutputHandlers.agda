{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.Network as Network
open import LibraBFT.Impl.Consensus.RoundManager as RoundManager
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

-- This module defines the handler for our implementation.  For most message types, it does some
-- initial validation before passing the message on to the proper handlers.

module LibraBFT.Impl.IO.OBM.InputOutputHandlers where

epvv : LBFT (Epoch × ValidatorVerifier)
epvv = _,_ <$> gets (_^∙ rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdEpoch)
           <*> gets (_^∙ rmEpochState ∙ esVerifier)

module handleProposal (now : Instant) (pm : ProposalMsg) where
  step₀ : LBFT Unit
  step₁ : Epoch → ValidatorVerifier → LBFT Unit

  step₀ = do
    (myEpoch , vv) ← epvv
    step₁ myEpoch vv

  step₁ myEpoch vv = do
    caseM⊎ Network.processProposal {- {!!} -} pm myEpoch vv of λ where
      (Left (Left _))  → logErr
      (Left (Right _)) → logInfo
      (Right _)        → RoundManager.processProposalMsgM now pm

handleProposal : Instant → ProposalMsg → LBFT Unit
handleProposal = handleProposal.step₀

handle : NodeId → NetworkMsg → Instant → LBFT Unit
handle _self msg now =
  case msg of λ where
    (P pm) → handleProposal now pm
    (V vm) → {!!} -- TODO-1: processVote now v
    (C cm) → return unit    -- We don't do anything with commit messages, they are just for defining Correctness.
