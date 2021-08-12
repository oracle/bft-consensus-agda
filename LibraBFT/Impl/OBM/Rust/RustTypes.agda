{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Rust.RustTypes where

-- TODO-2 : reasoning about integer overflow

F64 : Set
F64 = ℕ -- TODO-1 : this is 'Double' in Haskell

U64 : Set
U64 = ℕ

U128 : Set
U128 = ℕ

Usize : Set
Usize = ℕ

postulate
  VecDeque : Set
  vdNew : VecDeque


