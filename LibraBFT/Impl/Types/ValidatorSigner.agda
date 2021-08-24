{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS                           as PKCS hiding (sign)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.Types.ValidatorSigner where

sign : {C : Set} ⦃ enc : Encoder C ⦄ → ValidatorSigner → C → Signature
sign (ValidatorSigner∙new _ sk) c = PKCS.sign-encodable c sk

postulate -- TODO-1: publicKey_USE_ONLY_AT_INIT
  publicKey_USE_ONLY_AT_INIT : ValidatorSigner → PK
