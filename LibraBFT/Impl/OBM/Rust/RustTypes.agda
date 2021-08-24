{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude
------------------------------------------------------------------------------
open import Agda.Builtin.Float

module LibraBFT.Impl.OBM.Rust.RustTypes where

-- TODO-2 : reasoning about integer overflow

F64 : Set
F64 = Float -- This is 'Double' in Haskell.  In Agda, 'Float' is represented as a Haskell 'Double'.

U64 : Set
U64 = ℕ

U128 : Set
U128 = ℕ

Usize : Set
Usize = ℕ

postulate -- TODO-1: VecDeque, vdNew
  VecDeque : Set
  vdNew : VecDeque


