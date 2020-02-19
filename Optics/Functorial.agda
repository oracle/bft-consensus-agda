open import Level
open import Function
open import Category.Functor
open import Relation.Binary.PropositionalEquality

module Optics.Functorial where

  Lens' : (F : Set → Set) → RawFunctor F → Set → Set → Set
  Lens' F _ S A = (A → F A) → S → F S

  data Lens (S A : Set) : Set₁ where
    lens : ((F : Set → Set)(rf : RawFunctor F) → Lens' F rf S A)
         → Lens S A

  private
    cf : {A : Set} → RawFunctor (const A)
    cf = record { _<$>_ = λ x x₁ → x₁ }

    if : RawFunctor {Level.zero} id
    if = record { _<$>_ = λ x x₁ → x x₁ }

  -- Getter:

  -- this is typed as ^\. 
  _^∙_ : ∀{S A} → S → Lens S A → A
  _^∙_ {_} {A} s (lens p) = p (const A) cf id s

   -- Setter:

  set : ∀{S A} → S → Lens S A → A → S
  set s (lens p) a = p id if (const a) s
  syntax set s p a = s [ p := a ]

  -- Modifier:
  
  over : ∀{S A} → S → Lens S A → (A → A) → S
  over s (lens p) f = p id if f s
  syntax over s p f = s [ p %~ f ]


  -- Composition

  infixr 30 _∙_
  _∙_ : ∀{S A B} → Lens S A → Lens A B → Lens S B
  (lens p) ∙ (lens q) = lens (λ F rf x x₁ → p F rf (q F rf x) x₁)
