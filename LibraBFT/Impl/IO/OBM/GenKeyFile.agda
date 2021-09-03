{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.IO.OBM.GenKeyFile where

NfLiwsVssVvPe =
  (U64 × LedgerInfoWithSignatures × List ValidatorSigner × ValidatorVerifier × ProposerElection)
