{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

open StateInvariants
open StateTransProps

module LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers where

module epvvSpec where

  contract
    : ∀ pre Post
      → let ep = pre ^∙ pssSafetyData-rm ∙ sdEpoch
            vv = pre ^∙ rmEpochState ∙ esVerifier in
        (Post (ep , vv) pre [])
      → LBFT-weakestPre epvv Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl = pf

module handleProposalSpec (now : Instant) (pm : ProposalMsg) where

  open handleProposal now pm

  record Contract (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      -- General properties / invariants
      rmInv              : Preserves RoundManagerInv pre post
      noEpochChange      : NoEpochChange pre post
      -- Voting
      voteAttemptCorrect : Voting.VoteAttemptCorrectWithEpochReq pre post outs (pm ^∙ pmProposal)
      -- Signatures sent
      outQcs∈RM          : QC.OutputQc∈RoundManager outs pre -- could also be post, see which is more convenient

  contract : ∀ pre → LBFT-weakestPre (handleProposal now pm) (Contract pre) pre
  contract pre =
    epvvSpec.contract pre
      (RWST-weakestPre-bindPost unit (λ where (myEpoch , vv) → step₁ myEpoch vv) (Contract pre))
      contract-step₁
    where
    contractBail : ∀ outs → OutputProps.NoMsgs outs → Contract pre unit pre outs
    contractBail outs noMsgs =
      mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
        (Voting.mkVoteAttemptCorrectWithEpochReq (Voting.voteAttemptBailed outs noMsgs) tt)
        obm-dangerous-magic! -- TODO-2: prove it, ...

    contract-step₁ : _
    proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₁ e)  pp≡Left =
      contractBail _ refl
    proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₂ i) pp≡Left =
      contractBail _ refl
    proj₂ (contract-step₁ (myEpoch@._ , vv@._) refl) unit pp≡Right =
      processProposalMsgMSpec.contract now pm pre (Contract pre) pf
      where
      module PPM = processProposalMsgMSpec now pm

      sdEpoch≡ : pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ pm ^∙ pmProposal ∙ bEpoch
      sdEpoch≡
        with processProposalSpec.contract pm myEpoch vv
      ...| con rewrite pp≡Right = sym con

      pf : RWST-Post-⇒ (PPM.Contract pre) (Contract pre)
      pf unit st outs (processProposalMsgMSpec.mkContract rmInv noEpochChange voteAttemptCorrect) =
        mkContract rmInv noEpochChange
          (Voting.mkVoteAttemptCorrectWithEpochReq voteAttemptCorrect
            (Voting.voteAttemptEpochReq! voteAttemptCorrect sdEpoch≡))
          obm-dangerous-magic! -- TODO-2: prove it, ...

  contract! : ∀ pre → LBFT-Post-True (Contract pre) (handleProposal now pm) pre
  contract! pre = LBFT-contract (handleProposal now pm) (Contract pre) pre (contract pre)

  contract!-RoundManagerInv : ∀ pre → LBFT-Post-True (λ r st outs → Preserves RoundManagerInv pre st) (handleProposal now pm) pre
  contract!-RoundManagerInv pre = Contract.rmInv (contract! pre)
