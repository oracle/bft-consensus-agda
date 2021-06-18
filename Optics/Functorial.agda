{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Category.Functor
open import Data.Maybe
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

module Optics.Functorial where

  Lens' : (F : Set → Set) → RawFunctor F → Set → Set → Set
  Lens' F _ S A = (A → F A) → S → F S

  data Lens (S A : Set) : Set₁ where
    lens : ((F : Set → Set)(rf : RawFunctor F) → Lens' F rf S A)
         → Lens S A

  private
    cf : {A : Set} → RawFunctor {Level.zero} (const A)
    cf = record { _<$>_ = λ x x₁ → x₁ }

    if : RawFunctor {Level.zero} id
    if = record { _<$>_ = λ x x₁ → x x₁ }

  -- We can make lenses relatively painlessly without requiring reflection
  -- by providing getter and setter functions
  mkLens' : ∀ {A B : Set}
          → (B → A)
          → (B → A → B)
          → Lens B A
  mkLens' {A} {B} get set =
    lens (λ F rf f b → Category.Functor.RawFunctor._<$>_
                         {F = F} rf
                         {A = A}
                         {B = B}
                         (set b)
                         (f (get b)))

  -- Getter:

  -- this is typed as ^\.
  _^∙_ : ∀{S A} → S → Lens S A → A
  _^∙_ {_} {A} s (lens p) = p (const A) cf id s

   -- Setter:

  set : ∀{S A} → Lens S A → A → S → S
  set (lens p) a s = p id if (const a) s
  syntax set p a s = s [ p := a ]

  set? : ∀{S A} → Lens S (Maybe A) → A → S → S
  set? l a s = s [ l := just a ]
  syntax set? l a s = s [ l ?= a ]

  -- Modifier:

  over : ∀{S A} → Lens S A → (A → A) → S → S
  over (lens p) f s = p id if f s
  syntax over p f s = s [ p %~ f ]


  -- Composition

  infixr 30 _∙_
  _∙_ : ∀{S A B} → Lens S A → Lens A B → Lens S B
  (lens p) ∙ (lens q) = lens (λ F rf x x₁ → p F rf (q F rf x) x₁)
