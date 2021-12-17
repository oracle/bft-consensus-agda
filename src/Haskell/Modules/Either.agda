{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Modules.Either where

open import Data.Bool using (Bool; true; false; not)
import      Data.Sum  as DS renaming ([_,_] to either)
open import Function  using (_∘_)
open import Level           renaming (_⊔_ to _ℓ⊔_)

Either : ∀ {a b} → Set a → Set b → Set (a ℓ⊔ b)
Either A B = A DS.⊎ B
pattern Left  x = DS.inj₁ x
pattern Right x = DS.inj₂ x

either = DS.either

isLeft : ∀ {a b} {A : Set a} {B : Set b} → Either A B → Bool
isLeft (Left _)  = true
isLeft (Right _) = false

isRight : ∀ {a b} {A : Set a} {B : Set b} → Either A B → Bool
isRight = not ∘ isLeft


