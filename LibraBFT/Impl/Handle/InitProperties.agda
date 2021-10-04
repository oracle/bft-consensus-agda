{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
import      LibraBFT.Impl.Properties.Util             as Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Handle.InitProperties where

module realHandlerSpec
  (pid : Author)
  (bsi : BootstrapInfo)
  where

  import LibraBFT.Impl.Handle as Handle
  open   Handle.RealHandler --bsi
  import LibraBFT.Yasm.Types as LYT

  record ContractOk (rm : RoundManager) (acts : List (LYT.Action NetworkMsg)) : Set where
  -- Note that this contract is written in terms of the ACTIONS produced by the initialisation
  -- handler, whereas for other handlers, Contracts are in terms of the OUTPUTS they produce.  This
  -- makes sense because initialisation does not happen within the LBFT monad, and therefore there
  -- are no Outputs to translate to Actions.
    constructor mkContractOk
    field
      rmInv   : Util.Invariants.RoundManagerInv rm
      sigs∈bs : ∀ {vs qc}
              → vs              ∈     qcVotes qc
              → qc Util.QCProps.∈RoundManager rm
              → ∈BootstrapInfo-impl bsi (proj₂ vs)
      -- This will be easy to prove for now, because initialisation does not send any messages, but
      -- this generality enables it to do so in future.
      genSigs : ∀ {m vs qc} → LYT.send m ∈ acts → qc QC∈NM m → (vs ∈ qcVotes qc)
                → ∈BootstrapInfo-impl fakeBootstrapInfo (proj₂ vs)

  Contract : Maybe (RoundManager × List (LYT.Action NetworkMsg)) → Set
  Contract nothing            = ⊤
  Contract (just (rm , acts)) = ContractOk rm acts

  open import LibraBFT.Impl.Handle

  postulate
    contract : ∀ {x} → realHandler pid bsi ≡ x → Contract x
    -- contract = EitherD-contract {!!} Contract contract'

