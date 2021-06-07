{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude
import      LibraBFT.Base.PKCS             as PKCS
open        PKCS hiding (sign)
open import LibraBFT.Impl.Consensus.Types
import      LibraBFT.Impl.Util.Crypto           as Crypto
open import Optics.All

module LibraBFT.Impl.Types.ValidatorSigner where

sign : {C : Set} ⦃ ws : WithSig C ⦄ → ValidatorSigner → C → Signature
sign (ValidatorSigner∙new _ sk) c = PKCS.sign c sk
