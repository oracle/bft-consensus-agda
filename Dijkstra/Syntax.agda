{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.Syntax where

open import Dijkstra.EitherD
open import Dijkstra.EitherLike
open import Dijkstra.RWS
open import Haskell.Prelude
open import Optics.All

{-
Within a "Dijkstra-fied" monad `M`, `if` and `ifD` are semantically interchangeable.

The difference is in how proof obligations are generated
- with the *D variants generating new weakestPre obligations for each case.

In some cases, this is helpful for structuring proofs, while in other cases it is
unnecessary and introduces more structure to the proof without adding any benefit.

A rule of thumb is that, if the "scrutinee" (whatever we are doing case analysis on,
i.e., the first argument) is the value provided via >>= (bind) by a previous code block,
then we already have a weakestPre proof obligation, so introducing additional ones via the
*D variants only creates more work and provides no additional benefit.
-}

record MonadIfD {ℓ₁ ℓ₂ ℓ₃ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁ ℓ⊔ ℓ+1 ℓ₃) where
  infix 1 ifD‖_
  field
    ⦃ monad ⦄ : Monad M
    ifD‖_ : ∀ {A : Set ℓ₁} → Guards{ℓ₂}{ℓ₃} (M A) → M A

open MonadIfD ⦃ ... ⦄ public

module _ {ℓ₁ ℓ₂ ℓ₃} {M : Set ℓ₁ → Set ℓ₂} where

  private
    variable
      A : Set ℓ₁
      B : Set ℓ₃

  infix 0 ifD_then_else_
  ifD_then_else_ : ⦃ _ : MonadIfD{ℓ₃ = ℓ₃} M ⦄ ⦃ _ : ToBool B ⦄ → B → (c₁ c₂ : M A) → M A
  ifD b then c₁ else c₂ =
    ifD‖ b ≔ c₁
       ‖ otherwise≔ c₂

whenD : ∀ {ℓ₂ ℓ₃} {M : Set → Set ℓ₂} {B : Set ℓ₃} ⦃ _ : MonadIfD{ℓ0}{ℓ₂}{ℓ₃} M ⦄ ⦃ _ : ToBool B ⦄ → B → M Unit → M Unit
whenD b f = ifD b then f else pure unit

module _ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} where
  private
    variable A B : Set ℓ₁

  ifMD : ⦃ mi : MonadIfD{ℓ₃ = ℓ₁} M ⦄ ⦃ _ : ToBool B ⦄ → M B → (c₁ c₂ : M A) → M A
  ifMD{B = B} ⦃ mi ⦄ m c₁ c₂ = do
    x ← m
    ifD x then c₁ else c₂

record MonadMaybeD {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  field
    ⦃ monad ⦄ : Monad M
    maybeSD : ∀ {A B : Set ℓ₁} → Maybe A → M B → (A → M B) → M B

open MonadMaybeD ⦃ ... ⦄ public

infix 0 caseMD_of_
caseMD_of_ : ∀ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : MonadMaybeD M ⦄ {A B : Set ℓ₁} → Maybe A → (Maybe A → M B) → M B
caseMD m of f = maybeSD m (f nothing) (f ∘ just)

record MonadEitherD {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  field
    ⦃ monad ⦄ : Monad M
    eitherSD : ∀ {E A B : Set ℓ₁} → Either E A → (E → M B) → (A → M B) → M B

open MonadEitherD ⦃ ... ⦄ public hiding (eitherSD)

eitherSD
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {M : Set ℓ₁ → Set ℓ₂} ⦃ med : MonadEitherD M ⦄ →
    ∀ {EL : Set ℓ₁ → Set ℓ₁ → Set ℓ₃} ⦃ _ : EitherLike EL ⦄ →
    ∀ {E A B : Set ℓ₁} → EL E A → (E → M B) → (A → M B) → M B
eitherSD ⦃ med = med ⦄ e f₁ f₂ =
  MonadEitherD.eitherSD med (toEither e) f₁ f₂

infix 0 case⊎D_of_
case⊎D_of_
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : MonadEitherD M ⦄ →
    ∀ {EL : Set ℓ₁ → Set ℓ₁ → Set ℓ₃} ⦃ _ : EitherLike EL ⦄ →
    ∀ {E A B : Set ℓ₁} → EL E A → (EL E A → M B) → M B
case⊎D e of f = eitherSD e (f ∘ fromEither ∘ Left) (f ∘ fromEither ∘ Right)
