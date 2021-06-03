{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
import      LibraBFT.Yasm.Types as LYT
open import Optics.All

module LibraBFT.Impl.Types.LedgerInfoWithSignatures where

addSignature : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addSignature validator sig liws =
  case (Map.lookup validator (liws ^∙ liwsSignatures)) of λ where
    (just existing) → liws
    nothing         → LedgerInfoWithSignatures∙new
                        (liws ^∙ liwsLedgerInfo)
                        (Map.kvm-insert-Haskell validator sig Map.empty)



