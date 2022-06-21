{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Syntax where

open import Level renaming (_⊔_ to _ℓ⊔_ ; suc to ℓ+1)

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

instance
  open import Dijkstra.AST.Core

  MonadAST : ∀ {OP : ASTOps} → Monad (AST OP)
  Monad.return MonadAST = ASTreturn
  Monad._>>=_  MonadAST = ASTbind

