{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Types.LedgerInfoWithSignatures as LedgerInfoWithSignatures
open import LibraBFT.Prelude

module LibraBFT.Impl.Types.ValidatorVerifier where

checkVotingPower : ValidatorVerifier → List AccountAddress → VerifyError ⊎ Unit
checkVotingPower self authors = inj₁ (TooLittleVotingPower 0 0) -- HC-TODO



