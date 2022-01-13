{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Types.LedgerInfoWithSignatures as LedgerInfoWithSignatures
open import LibraBFT.ImplShared.Consensus.Types
open import Util.PKCS

module LibraBFT.Impl.Types.CryptoProxies where

addToLi : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addToLi = LedgerInfoWithSignatures.addSignature

