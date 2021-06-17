{-# OPTIONS --allow-unsolved-metas #-}

{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Impl.Types.LedgerInfoWithSignatures as LedgerInfoWithSignatures
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS as PKCS hiding (sign)
open import Optics.All

module LibraBFT.Impl.Types.ValidatorSigner where

sign : ∀ {A : Set} → ValidatorSigner → A → Signature
sign = {!!}
