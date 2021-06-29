{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Hash
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures    as LedgerInfoWithSignatures
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

open RWST-do

module LibraBFT.Impl.Types.Properties.LedgerInfoWithSignatures (self : LedgerInfoWithSignatures) (vv : ValidatorVerifier) where

  -- See comments in LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert

  postulate -- TODO-2: define and prove

    Contract : Set

    contract : LedgerInfoWithSignatures.verifySignatures self vv ≡ Right unit → Contract
