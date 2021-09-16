{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
import      LibraBFT.Impl.Properties.Util             as Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Handle.InitProperties where

module initEMWithOutputSpec where

  record ContractOk (em : EpochManager) (lo : List Output) : Set where
    constructor mkContractOk
    field
       rmInv : Σ RoundManager
                 λ rm → em ^∙ emProcessor ≡ just (RoundProcessorNormal rm)
                      × Util.Invariants.RoundManagerInv rm

  Contract : Either ErrLog (EpochManager × List Output) → Set
  Contract (Left _)          = ⊤
  Contract (Right (em , lo)) = ContractOk em lo

--  open initEMWithOutputSpec

  -- module _ (bt“ : BlockTree) (b : ExecutedBlock) (con : ContractOk bt“ b) where
  -- postulate
  --   contract' : EitherD-weakestPre (step₀ block bt) Contract

  -- contract : Contract (initEMWithOutput.E block bt)
  -- contract = EitherD-contract (step₀ block bt) Contract contract'

