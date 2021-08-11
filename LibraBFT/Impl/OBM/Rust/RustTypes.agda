{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Rust.RustTypes where

U64 : Set
U64 = ℕ

Usize : Set
Usize = ℕ

data VecDeque : Set where

postulate
  vdNew : VecDeque


