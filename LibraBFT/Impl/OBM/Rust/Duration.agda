{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.OBM.Rust.RustTypes

module LibraBFT.Impl.OBM.Rust.Duration where

record Duration : Set where
  constructor Duration∙new

postulate -- TODO-1 : fromMillis, asMillis
  fromMillis : U64 → Duration
  asMillis   : Duration → U128
