{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.EitherLike where

open import Haskell.Prelude

open import Level
  renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
  public

module _ {ℓ₀ ℓ₁ ℓ₂ : Level} where
  EL-type = Set ℓ₁ → Set ℓ₂ → Set ℓ₀
  EL-level = ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₀

  -- Utility to make passing between `Either` and `EitherD` more convenient
  record EitherLike (E : EL-type) : Set (ℓ+1 EL-level) where
    field
      fromEither : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → Either A B → E A B
      toEither   : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → E A B → Either A B
  open EitherLike ⦃ ... ⦄ public

  EL-func : EL-type → Set (ℓ+1 EL-level)
  EL-func EL = ⦃ mel : EitherLike EL ⦄ → Set EL-level

instance
  EitherLike-Either : ∀ {ℓ₁ ℓ₂} → EitherLike{ℓ₁ ℓ⊔ ℓ₂}{ℓ₁}{ℓ₂} Either
  EitherLike.fromEither EitherLike-Either = id
  EitherLike.toEither   EitherLike-Either = id

