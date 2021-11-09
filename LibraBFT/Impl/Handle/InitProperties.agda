{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.Handle
open        InitHandler
import      LibraBFT.Impl.Properties.Util             as Util
import      LibraBFT.Impl.Types.ValidatorSigner       as ValidatorSigner
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Types as LYT
open import Optics.All

module LibraBFT.Impl.Handle.InitProperties where

------------------------------------------------------------------------------

-- RoundManager properties

_IsNormalRoundManagerOf_ : RoundManager → EpochManager → Set
_IsNormalRoundManagerOf_ rm em =
  em ^∙ emProcessor ≡ just (RoundProcessorNormal rm)

IsNormalRoundManagerOf-inj :
  ∀ {em} {rm1} {rm2}
  → rm1 IsNormalRoundManagerOf em
  → rm2 IsNormalRoundManagerOf em
  → rm1 ≡ rm2
IsNormalRoundManagerOf-inj refl refl = refl

InitSdLVNothing : RoundManager → Set
InitSdLVNothing rm = rm ^∙ rmSafetyRules ∙ srPersistentStorage
                         ∙ pssSafetyData ∙ sdLastVote ≡ nothing

InitSigs∈bs : RoundManager → Set
InitSigs∈bs rm = ∀ {bsi vs qc}
                 → vs              ∈     qcVotes qc
                 → qc Util.QCProps.∈RoundManager rm
                 → ∈BootstrapInfo-impl bsi (proj₂ vs)

-- Message properties

-- During epoch initialisation, no messages are sent
-- EXCEPT the leader of Round 1 SENDS a ProposalMsg during initialization.
-- Rust/Haskell impls do not include signatures in the genesis QC's LIWS.
-- The initial proposal for (Epoch N) (Round 1) is built on a QC with empty signatures.

InitIsInitPM' : NetworkMsg → Set
InitIsInitPM' m = ∃[ pm ] ( m ≡ P pm
                          × ∀ {vs qc}
                          → vs   ∈ qcVotes qc
                          → qc QC∈NM       m
                          → ⊥)

InitIsInitPM : List (LYT.Action NetworkMsg) → Set
InitIsInitPM acts = ∀ {m}
                    → LYT.send m ∈ acts
                    → InitIsInitPM' m

------------------------------------------------------------------------------

open Util.Invariants

module getEmRmSpec
  (em : EpochManager)
  where

  Contract : EitherD-Post ErrLog RoundManager
  Contract (Left x)   = ⊤
  Contract (Right rm) = rm IsNormalRoundManagerOf em

  contract' : EitherD-weakestPre (getEmRm-ed-abs em) Contract
  contract' rewrite getEmRm-ed-abs≡
     with em ^∙ emProcessor | inspect (_^∙ emProcessor) em
  ...| nothing | _ = tt
  ...| just (RoundProcessorRecovery x) | _     = tt
  ...| just (RoundProcessorNormal   x) | [ refl ] = refl

record InitContractOk (rm : RoundManager) (outs : List Output) : Set where
  constructor mkInitContractOk
  field
    rmInv       : RoundManagerInv rm
    sdLVNothing : InitSdLVNothing rm
    sigs∈bs     : InitSigs∈bs rm
    isInitPM    : InitIsInitPM (outputsToActions {State = rm} outs)
open InitContractOk

EMInitCond : EpochManager × List Output → Set
EMInitCond (em , outs) = ∃[ rm ] ( rm IsNormalRoundManagerOf em × InitContractOk rm outs )

module initEMWithOutputSpec
  (bsi : BootstrapInfo)
  (vs  : ValidatorSigner)
  where

  Contract : EitherD-Post ErrLog (EpochManager × List Output)
  Contract (Left x)        = ⊤
  Contract (Right em×outs) = EMInitCond em×outs

  postulate
    contract' : EitherD-weakestPre (initEMWithOutput-ed-abs bsi vs) Contract

module initRMWithOutputSpec
  (bsi : BootstrapInfo)
  (vs  : ValidatorSigner)
  where

  Contract : EitherD-Post ErrLog (RoundManager × List Output)
  Contract (Left x)            = ⊤
  Contract (Right (rm , outs)) = InitContractOk rm outs

  open initRMWithOutput-ed bsi vs

  contract-step₁ : ∀ {em lo}
                   → EMInitCond (em , lo)
                   → EitherD-weakestPre (step₁ (em , lo)) Contract
  contract-step₁ {em} {lo} (rm , inrm , cntrctOk) =
    EitherD-⇒-bind (getEmRm-ed-abs em)
                   (getEmRmSpec.contract' em)
                   P⇒Q
     where
       P⇒Q : EitherD-Post-⇒ (getEmRmSpec.Contract em)
                            (EitherD-weakestPre-bindPost (λ rm → RightD (rm , lo)) Contract)
       P⇒Q (Left x) _ = tt
       P⇒Q (Right rm') pf .rm' refl rewrite IsNormalRoundManagerOf-inj {em} inrm pf = cntrctOk

  contract' : EitherD-weakestPre (initRMWithOutput-ed-abs bsi vs) Contract
  contract' rewrite initRMWithOutput-ed-abs≡ =
    EitherD-⇒-bind (initEMWithOutput-ed-abs bsi vs)
                   (initEMWithOutputSpec.contract' bsi vs)
                   P⇒Q
      where
      P⇒Q : EitherD-Post-⇒ (initEMWithOutputSpec.Contract bsi vs) _
      P⇒Q (Left x) _ = tt
      P⇒Q (Right (em , lo)) pf .(em , lo) refl = contract-step₁ pf

  contract : Contract (initRMWithOutput-e-abs bsi vs)
  contract rewrite initRMWithOutput≡ {bsi} {vs} =
    EitherD-contract (initRMWithOutput-ed-abs bsi vs) Contract contract'

------------------------------------------------------------------------------

module initHandlerSpec
  (pid : Author)
  (bsi : BootstrapInfo)
  where

  record ContractOk (rm : RoundManager) (acts : List (LYT.Action NetworkMsg)) : Set where
    constructor mkContractOk
    field
      rmInv       : Util.Invariants.RoundManagerInv rm
      sdLVNothing : InitSdLVNothing rm
      sigs∈bs     : InitSigs∈bs rm
      isInitPM    : InitIsInitPM acts
      -- TODO-3: We will eventually need to know that our ValidatorSigner is for the correct peer,
      -- because it will be needed to prove impl-sps-avp : StepPeerState-AllValidParts

  Contract : Maybe (RoundManager × List (LYT.Action NetworkMsg)) → Set
  Contract nothing            = ⊤
  Contract (just (rm , acts)) = ContractOk rm acts

  -- TODO-2: this property is more succinctly/elegantly stated as Contract (initHandler pid bsi),
  -- and can be proved by starting the proof as follows:
  --
  -- contract : Contract (initHandler pid bsi)
  -- contract with initHandler pid bsi | inspect (initHandler pid) bsi
  -- ...| nothing | _ = tt
  -- ...| just (rm , acts) | [ hndl≡just ]
  --
  -- However, this breaks a bunch of proofs that use this, so not doing it for now.
  contract : ∀ {x} → initHandler pid bsi ≡ x → Contract x
  contract {nothing} hndl≡nothing rewrite sym hndl≡nothing = tt
  contract {just (rm , acts)} hndl≡just
    with ValidatorSigner.obmGetValidatorSigner pid  (bsi ^∙ bsiVSS)
  ...| Left _ = absurd nothing ≡ just _ case hndl≡just  of λ ()
  ...| Right vs
    with initRMWithOutputSpec.contract bsi vs
  ...| initRMWithOutputContractOk
    with initRMWithOutput-e-abs bsi vs
  ...| Left _ = absurd nothing ≡ just (rm , acts) case hndl≡just of λ ()
  ...| Right rm×outs rewrite sym (cong proj₂ (just-injective hndl≡just)) |
                                 (cong proj₁ (just-injective hndl≡just)) =
       mkContractOk
         (InitContractOk.rmInv       initRMWithOutputContractOk)
         (InitContractOk.sdLVNothing initRMWithOutputContractOk)
         (InitContractOk.sigs∈bs     initRMWithOutputContractOk)
         (InitContractOk.isInitPM    initRMWithOutputContractOk)
