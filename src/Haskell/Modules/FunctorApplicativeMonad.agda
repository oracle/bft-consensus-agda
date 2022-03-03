{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Modules.FunctorApplicativeMonad where

open import Haskell.Modules.Either
------------------------------------------------------------------------------
open import Data.List
open import Data.Maybe renaming (_>>=_ to _Maybe->>=_)
open import Function
open import Level renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
open import Relation.Binary.PropositionalEquality

record Functor  {ℓ₁ ℓ₂ : Level} (F : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 4 _<$>_
  field
    _<$>_ : ∀ {A B : Set ℓ₁} → (A → B) → F A → F B
  fmap = _<$>_
open Functor ⦃ ... ⦄ public

record Applicative {ℓ₁ ℓ₂ : Level} (F : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 4 _<*>_
  field
    pure  : ∀ {A : Set ℓ₁} → A → F A
    _<*>_ : ∀ {A B : Set ℓ₁} → F (A → B) → F A → F B
open Applicative ⦃ ... ⦄ public
instance
  ApplicativeFunctor : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} ⦃ _ : Applicative F ⦄ → Functor F
  Functor._<$>_ ApplicativeFunctor f xs = pure f <*> xs

record Monad {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 1 _>>=_ _>>_
  field
    return : ∀ {A : Set ℓ₁} → A → M A
    _>>=_  : ∀ {A B : Set ℓ₁} → M A → (A → M B) → M B

  _>>_ : ∀ {A B : Set ℓ₁} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂
open Monad ⦃ ... ⦄ public

record MonadLaws
  {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) ⦃ m : Monad M ⦄
  (_~_ : {A : Set ℓ₁} → M A → M A → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  field
    idLeft  : ∀ {A B : Set ℓ₁} → (x : A) (f : A → M B)
              → (return x >>= f) ~ f x
    idRight : ∀ {A : Set ℓ₁} → (m : M A)
              → (m >>= return) ~ m
    assoc   : ∀ {A B C : Set ℓ₁} → (m : M A) (f : A → M B) (g : B → M C)
              → ((m >>= f) >>= g) ~ (m >>= (λ x → f x >>= g))

instance
  MonadApplicative : ∀ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄ → Applicative M
  Applicative.pure  MonadApplicative       = return
  Applicative._<*>_ MonadApplicative fs xs = do
    f ← fs
    x ← xs
    return (f x)

instance
  Monad-Either : ∀ {ℓ}{C : Set ℓ} → Monad{ℓ}{ℓ} (Either C)
  Monad.return (Monad-Either{ℓ}{C}) = Right
  Monad._>>=_  (Monad-Either{ℓ}{C}) = either (const ∘ Left) _|>_

  Monad-Maybe : ∀ {ℓ} → Monad {ℓ} {ℓ} Maybe
  Monad.return (Monad-Maybe{ℓ}) = just
  Monad._>>=_  (Monad-Maybe{ℓ}) = _Maybe->>=_

  Monad-List : ∀ {ℓ} → Monad {ℓ}{ℓ} List
  Monad.return Monad-List x   = x ∷ []
  Monad._>>=_  Monad-List x f = concat (Data.List.map f x)

