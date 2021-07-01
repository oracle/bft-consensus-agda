{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS                  as PKCS hiding (sign; verify)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Crypto where

record CryptoHash (A : Set) : Set where
  field
    sign        : SK → A → Signature
    verify      : {-Text-} PK → Signature → A → Either ErrLog Unit
    ⦃ encodeA ⦄ : Encoder A

open CryptoHash ⦃ ... ⦄ public

instance
  CryptoHashLedgerInfo : CryptoHash LedgerInfo
  CryptoHashLedgerInfo = record
    { sign   = λ sk li     → PKCS.sign-raw  (encode li)     sk
    ; verify = λ pk sig li → if PKCS.verify (encode li) sig pk
                             then Right unit
                             else Left fakeErr }
