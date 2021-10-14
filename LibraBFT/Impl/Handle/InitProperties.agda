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

module initHandlerSpec
  (pid : Author)
  (bsi : BootstrapInfo)
  where

  import      LibraBFT.Yasm.Types as LYT

  record ContractOk (rm : RoundManager) (acts : List (LYT.Action NetworkMsg)) : Set where
    constructor mkContractOk
    field
      rmInv   : Util.Invariants.RoundManagerInv rm
      sigs∈bs : ∀ {vs qc}
              → vs              ∈     qcVotes qc
              → qc Util.QCProps.∈RoundManager rm
              → ∈BootstrapInfo-impl bsi (proj₂ vs)
      -- During epoch initialisation, no messages are sent
      -- EXCEPT the leader of Round 1 SENDS a ProposalMsg during initialization.
      -- Rust/Haskell impls do not include signatures in the genesis QC's LIWS.
      -- The initial proposal for (Epoch N) (Round 1) is built on a QC with empty signatures.
      isInitPM : ∀ {m}
               → LYT.send m ∈ acts
               → ∃[ pm ] ( m ≡ P pm
                         × ∀ {vs qc}
                           → vs   ∈ qcVotes qc
                           → qc QC∈NM       m
                           → ⊥)

  Contract : Maybe (RoundManager × List (LYT.Action NetworkMsg)) → Set
  Contract nothing            = ⊤
  Contract (just (rm , acts)) = ContractOk rm acts

  import      LibraBFT.Impl.Handle as Handle
  open        Handle.InitHandler

  postulate
    contract : ∀ {x} → initHandler pid bsi ≡ x → Contract x
    -- contract = EitherD-contract {!!} Contract contract'

