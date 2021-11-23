{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.Handle
open        InitHandler
import      LibraBFT.Impl.IO.OBM.GenKeyFile           as GenKeyFile
import      LibraBFT.Impl.IO.OBM.Properties.Start     as Start
import      LibraBFT.Impl.Properties.Util             as Util
import      LibraBFT.Impl.Types.BlockInfo             as BlockInfo
import      LibraBFT.Impl.Types.ValidatorSigner       as ValidatorSigner
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Types as LYT
open import Optics.All

module LibraBFT.Impl.Handle.InitProperties where

------------------------------------------------------------------------------

------------------------------------------------------------------------------

open Util.Invariants
open Util.InitProofDefs

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

module initializeSpec
  (now : Instant)
  (nfl : GenKeyFile.NfLiwsVsVvPe)
  where

  contract' : EitherD-weakestPre (initialize-ed-abs now nfl) (InitContract nothing)
  contract' rewrite initialize-ed-abs≡ =
    Start.startViaConsensusProviderSpec.contract'
      now
      nfl
      (TxTypeDependentStuffForNetwork∙new proposalGenerator (StateComputer∙new BlockInfo.gENESIS_VERSION))

module initEMWithOutputSpec
  (bsi : BootstrapInfo)
  (vs  : ValidatorSigner)
  where

  contract' : EitherD-weakestPre (initEMWithOutput-ed-abs bsi vs) (InitContract nothing)
  contract' rewrite initEMWithOutput-ed-abs≡ = initializeSpec.contract' now (mkNfLiwsVsVvPe bsi vs)

module initRMWithOutputSpec
  (bsi : BootstrapInfo)
  (vs  : ValidatorSigner)
  where

  Contract : EitherD-Post ErrLog (RoundManager × List Output)
  Contract (Left x)            = ⊤
  Contract (Right (rm , outs)) = InitContractOk nothing rm outs

  open initRMWithOutput-ed bsi vs

  contract-step₁ : ∀ {em lo}
                   → EMInitCond nothing (em , lo)
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
      P⇒Q : EitherD-Post-⇒ (InitContract nothing) _
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
      sdLVnothing : InitSdLV≡ rm nothing
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
         (InitContractOk.sdLV≡       initRMWithOutputContractOk)
         (InitContractOk.sigs∈bs     initRMWithOutputContractOk)
         (InitContractOk.isInitPM    initRMWithOutputContractOk)
