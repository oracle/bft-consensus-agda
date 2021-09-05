{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS                  as PKCS hiding (sign; verify)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Crypto where

------------------------------------------------------------------------------
-- keys

postulate -- TODO-1 : makePK
  makePK : SK → PK

------------------------------------------------------------------------------

postulate -- TODO-1: implement obmHashVersion
  obmHashVersion : Version → HashValue

------------------------------------------------------------------------------
-- sign and verify

record CryptoHash (A : Set) : Set where
  field
    sign        : SK → A → Signature
    verify      : {-Text-} PK → Signature → A → Either ErrLog Unit
    ⦃ encodeA ⦄ : Encoder A

open CryptoHash ⦃ ... ⦄ public

instance
  CryptoHashBlockData : CryptoHash BlockData
  CryptoHashBlockData = record
    { sign   = λ sk bd     → PKCS.sign-raw  (encode bd)     sk
    ; verify = λ pk sig bd → if PKCS.verify (encode bd) sig pk
                             then Right unit
                             else Left fakeErr }

instance
  CryptoHashLedgerInfo : CryptoHash LedgerInfo
  CryptoHashLedgerInfo = record
    { sign   = λ sk li     → PKCS.sign-raw  (encode li)     sk
    ; verify = λ pk sig li → if PKCS.verify (encode li) sig pk
                             then Right unit
                             else Left fakeErr }

instance
  CryptoHashTimeout : CryptoHash Timeout
  CryptoHashTimeout = record
    { sign   = λ sk to     → PKCS.sign-raw  (encode to)     sk
    ; verify = λ pk sig to → if PKCS.verify (encode to) sig pk
                             then Right unit
                             else Left fakeErr }
