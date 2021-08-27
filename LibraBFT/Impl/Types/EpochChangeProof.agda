{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS                        hiding (verify)
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.Verifier              as Verifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.List.Base                            as List
import      Data.String                               as String

module LibraBFT.Impl.Types.EpochChangeProof where

postulate -- TODO-1: verify
  verify
   : {verifier : Set} ⦃ _ : Verifier.Verifier verifier ⦄
   → EpochChangeProof → verifier
   → Either ErrLog LedgerInfoWithSignatures
