{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.Records
open import LibraBFT.Impl.Consensus.Network
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.Network.Properties where

open Invariants

module processProposalSpec (proposal : ProposalMsg) (myEpoch : Epoch) (vv : ValidatorVerifier) where
  postulate -- TODO-2: Refine contract
    -- We also need to know that the the proposal message was successfully
    -- checked by `ProposalMsg.verify`
    contract
      : case (processProposal proposal myEpoch vv) of λ where
          (Left _) → Unit
          (Right _) → proposal ^∙ pmProposal ∙ bEpoch ≡ myEpoch
                      × BlockId-correct (proposal ^∙ pmProposal)

