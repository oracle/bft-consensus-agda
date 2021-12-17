{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Modules.Eq where

open import Haskell.Modules.ToBool
------------------------------------------------------------------------------
open import Data.Bool hiding (_≟_; not)
open import Data.List                               as DL
open import Data.Maybe using (Maybe; just; nothing)
import      Data.Nat                                as DN
open import Function using (_$_; _∘_)
import      Relation.Binary.PropositionalEquality   as PE using (_≡_; refl)
import      Relation.Nullary                        as RN

record Eq {a} (A : Set a) : Set a where
  infix 4 _≟_ _==_ _/=_
  field
    _≟_ : (a b : A) → RN.Dec (a PE.≡ b)

  _==_   : A → A → Bool
  a == b = toBool $ a ≟ b

  _/=_ : A → A → Bool
  a /= b = not (a == b)
open Eq ⦃ ... ⦄ public

import Data.List.Relation.Unary.Any as Any using (any)

elem : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → A → DL.List A → Bool
elem x = toBool ∘ Any.any (x ≟_)

instance
  Eq-Nat : Eq DN.ℕ
  Eq._≟_ Eq-Nat = DN._≟_

  Eq-Maybe : ∀ {a} {A : Set a} ⦃ _ : Eq A ⦄ → Eq (Maybe A)
  Eq._≟_ Eq-Maybe  nothing  nothing = RN.yes PE.refl
  Eq._≟_ Eq-Maybe (just _)  nothing = RN.no λ ()
  Eq._≟_ Eq-Maybe  nothing (just _) = RN.no λ ()
  Eq._≟_ Eq-Maybe (just a) (just b)
     with a ≟ b
  ... | RN.no  proof   = RN.no λ where PE.refl → proof PE.refl
  ... | RN.yes PE.refl = RN.yes PE.refl

