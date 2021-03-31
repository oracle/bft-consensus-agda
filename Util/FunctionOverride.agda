{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Axiom.Extensionality.Propositional
open import Data.Empty
open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

module Util.FunctionOverride
          {ℓ₁   : Level}
          (A    : Set ℓ₁)
          (_≟A_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂))
          {ℓ₂ : Level}{B : Set ℓ₂}
  where

  override : (A → B) → A → B → (A → B)
  override f p v x
    with p ≟A x
  ...| yes refl = v
  ...| no  neq  = f x

  syntax override m p v = ⟦ m , p ← v ⟧

  postulate
    funext : Extensionality ℓ₁ ℓ₂

  override-target-≡ : ∀ {a : A}{b : B}{f}
                    → override f a b a ≡ b
  override-target-≡ {a}
     with a ≟A a
  ...| yes refl = refl
  ...| no  neq  = ⊥-elim (neq refl)

  override-target-≢ : ∀ {a a' : A}{b : B}{f}
                    → a' ≢ a
                    → f a' ≡ (override f a b) a'
  override-target-≢ {a} {a'} neq
     with a ≟A a'
  ...| yes refl = ⊥-elim (neq refl)
  ...| no  _    = refl

  overrideAux : ∀ {f : A → B}
              → (p a : A)
              → override f p (f p) a ≡ f a
  overrideAux p a
    with p ≟A a
  ...| no neq   = refl
  ...| yes refl = refl

  override≡Correct : ∀ {f : A → B}{p : A} → override f p (f p) ≡ f
  override≡Correct {p = p} = funext (overrideAux p)
