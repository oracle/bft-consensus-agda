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

module initRMWithOutputSpec
  (bsi : BootstrapInfo)
  (vs  : ValidatorSigner)
  where

  record ContractOk (rm : RoundManager) (outs : List Output) : Set where
    constructor mkContractOk
    field
      rmInv       : Util.Invariants.RoundManagerInv rm
      sdLVNothing : InitSdLVNothing rm
      sigs∈bs     : InitSigs∈bs rm
      isInitPM    : InitIsInitPM (outputsToActions {State = rm} outs)
  open ContractOk

  Contract : EitherD-Post ErrLog (RoundManager × List Output)
  Contract (Left x)            = ⊤
  Contract (Right (rm , outs)) = ContractOk rm outs

--  postulate
  contract' : EitherD-weakestPre (initRMWithOutput-ed bsi vs) Contract
  contract' = {!initRMWithOutput-ed bsi vs!}
{-
xxx
    where
      xxx : EitherD-weakestPre (initEMWithOutput-ed-abs bsi vs) (EitherD-weakestPre-bindPost _ Contract)
      xxx 
         with EitherD-run (initEMWithOutput-ed-abs bsi vs)  -- NOPE, need to establish initEMWithOutputSpec, use contract
      ... | Left x  = {!!}
      ... | Right y = {!!}

      yyy : EitherD-weakestPre (initRMWithOutput-ed bsi vs) Contract
      yyy = xxx
-}



  {-  Apply EitherD-weakestpre (EitherD-bind m f) P rule
      m = initEMWithOutput-ed-abs bsi vs
      So need to prove something about initEMWithOutput
      Currently not abstract, so Agda looks into initEMWithOutput.
      Should we soldier on, looking into initEMWithOutput and making a fragile proof, or make an
      equivalent abstract version and a Contract for it?
  -}

  contract : Contract (initRMWithOutput-e-abs bsi vs)
  contract rewrite initRMWithOutput≡ {bsi} {vs} = EitherD-contract (initRMWithOutput-ed bsi vs) Contract contract'

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

  Contract : Maybe (RoundManager × List (LYT.Action NetworkMsg)) → Set
  Contract nothing            = ⊤
  Contract (just (rm , acts)) = ContractOk rm acts

  -- TODO: make more normal
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
         (initRMWithOutputSpec.ContractOk.rmInv       initRMWithOutputContractOk)
         (initRMWithOutputSpec.ContractOk.sdLVNothing initRMWithOutputContractOk)
         (initRMWithOutputSpec.ContractOk.sigs∈bs     initRMWithOutputContractOk)
         (initRMWithOutputSpec.ContractOk.isInitPM    initRMWithOutputContractOk)
