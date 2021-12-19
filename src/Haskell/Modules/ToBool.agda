{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Modules.ToBool where

open import Data.Bool hiding (not)
import      Function
import      Relation.Nullary                as RN
import      Relation.Nullary.Decidable.Core as RNDC

record ToBool {a}(A : Set a) : Set a where
  field
    toBool : A → Bool
open ToBool {{ ... }} public

not : ∀ {b} {B : Set b} ⦃ _ : ToBool B ⦄ → B → Bool
not b = Data.Bool.not (toBool b)

instance
  ToBool-Bool : ToBool Bool
  ToBool-Bool = record { toBool = Function.id }

  ToBool-Dec : ∀{a}{A : Set a} → ToBool (RN.Dec A)
  ToBool-Dec = record { toBool = RNDC.⌊_⌋ }



