{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties as RoundManagerProps
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

-- This module defines the handler for our implementation.  For most message types, it does some
-- initial validation before passing the message on to the proper handlers.

module LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers where

module handleProposalSpec (now : Instant) (pm : ProposalMsg) where

  record Contract-HasOuts
    (pre : RoundManager) (_ : Unit) (post : RoundManager) (msgs : List Output)
    (vm : VoteMsg) (pid : NodeId) : Set where
    constructor mkContract-HasOuts
    field
      msgs≡    : msgs ≡ SendVote vm (pid ∷ []) ∷ []
      ep≡      : pre ≡L vm at (lSafetyData ∙ sdEpoch , vmVote ∙ vEpoch)
      lvr-pre  : pre ^∙ lSafetyData ∙ sdLastVotedRound < vm ^∙ vmVote ∙ vRound
                 ⊎ just (vm ^∙ vmVote) ≡ (pre ^∙ lSafetyData ∙ sdLastVote)
      lvr-post : just (vm ^∙ vmVote) ≡ (post ^∙ lSafetyData ∙ sdLastVote)

  Contract : (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) → Set
  Contract pre r post outs =
    let msgs = List-filter isOutputMsg? outs in
    msgs ≡ [] ⊎ ∃₂ λ vm pid → Contract-HasOuts pre r post msgs vm pid


  contract : ∀ pre → RWST-weakestPre (handleProposal now pm) (Contract pre) unit pre
  proj₁ (contract pre ._ refl ._ refl ._ refl ._ refl) (Left x) e≡ = inj₁ refl
  proj₁ (contract pre ._ refl ._ refl ._ refl ._ refl) (Right y) e≡ = inj₁ refl
  proj₂ (contract pre ._ refl ._ refl ._ refl ._ refl) unit pp-pm≡
     with NetworkProps.processProposalSpec.contract pm (pre ^∙ lSafetyData ∙ sdEpoch) ((_rmEC pre) ^∙ rmEpochState ∙ esVerifier)
  ...| pf
     with Network.processProposal pm (pre ^∙ lSafetyData ∙ sdEpoch) ((_rmEC pre) ^∙ rmEpochState ∙ esVerifier)
  proj₂ (contract pre ._ refl ._ refl ._ refl ._ refl) unit refl | pf | .(Right unit) =
    processProposalMsgMSpec.contract⇒ now pm pre (Contract pre) help
    where
    help : ∀ r st outs
           → processProposalMsgMSpec.Contract now pm pre r st outs
           → Contract pre r st outs
    help r st outs (Left msgs≡[]) = Left msgs≡[]
    help r st outs (Right (vm , pid , processProposalMsgMSpec.mkContract-HasOuts msgs≡ ep≡ lvr-pre lvr-post)) =
      Right (vm , pid ,
             mkContract-HasOuts msgs≡ (trans (sym pf) ep≡) lvr-pre lvr-post)
