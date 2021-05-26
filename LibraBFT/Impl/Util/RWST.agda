{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude

-- This module defines syntax and functionality modeling an RWST monad,
-- which we use to define an implementation.
-- TODO-2: this module is independent of any particular implementation
-- and arguably belongs somewhere more general, such as next to Optics.

module LibraBFT.Impl.Util.RWST (ℓ-State : Level) where

  ----------------
  -- RWST Monad --
  ----------------

  -- 'Fake' RWST monad; fake in the sense
  -- we use the free monoid on the writer (aka. lists)
  -- instad of requiring it to be a monoid in a separate
  -- argument.
  RWST-Raw : Set → Set → Set ℓ-State → {ℓ-Result : Level} → Set ℓ-Result → Set (ℓ-State ℓ⊔ ℓ-Result)
  RWST-Raw Ev Wr St R = Ev → St → (R × St × List Wr)

  -- Wrap it in a type; prevents spurious evaluation and
  -- obliges us to 'run' the monad.
  data RWST (Ev Wr : Set) (St : Set ℓ-State) {ℓ-Result : Level} : Set ℓ-Result → Set (ℓ-State ℓ⊔ ℓ-Result) where
    rwst : ∀ {R : Set ℓ-Result} → RWST-Raw Ev Wr St {ℓ-Result} R → RWST Ev Wr St R

  private
   variable
    Ev Wr : Set
    ℓ-A ℓ-B : Level
    A : Set ℓ-A
    B : Set ℓ-B
    St : Set ℓ-State

  RWST-run : RWST Ev Wr St A → Ev → St → (A × St × List Wr)
  RWST-run (rwst f) = f

  RWST-bind : RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  RWST-bind x f = rwst (λ ev st →
    let (a , st'  , wr₀) = RWST-run x     ev st
        (b , st'' , wr₁) = RWST-run (f a) ev st'
     in b , st'' , wr₀ ++ wr₁)

  RWST-return : A → RWST Ev Wr St A
  RWST-return x = rwst (λ _ st → x , st , [])

  -- Functorial Functionality

  RWST-map : (A → B) → RWST Ev Wr St A → RWST Ev Wr St B
  RWST-map f x = rwst (λ ev st →
    let (a , st' , wr) = RWST-run x ev st
     in f a , st' , wr)

  -- Provided Functionality

  get : RWST Ev Wr St {ℓ-State} St
  get = rwst (λ _ st → st , st , [])

  gets : (St → A) → RWST Ev Wr St A
  gets f = RWST-bind get (RWST-return ∘ f)

{- TODO-2: extend Lens to work with different levels and reinstate this
  use : Lens St A → RWST Ev Wr St A
  use f = RWST-bind get (RWST-return ∘ (_^∙ f))
-}

  modify : (St → St) → RWST Ev Wr St Unit
  modify f = rwst (λ _ st → unit , f st , [])

{- TODO-2: extend Lens to work with different levels and reinstate this
  modify' : ∀ {A} → Lens St A → A → RWST Ev Wr St Unit
  modify' l val = modify λ x → x [ l := val ]
  syntax modify' l val = l ∙= val
-}

  put : St → RWST Ev Wr St Unit
  put s = modify (λ _ → s)

  tell : List Wr → RWST Ev Wr St Unit
  tell wrs = rwst (λ _ st → unit , st , wrs)

  tell1 : Wr → RWST Ev Wr St Unit
  tell1 wr = tell (wr ∷ [])


  ask : RWST Ev Wr St Ev
  ask = rwst (λ ev st → (ev , st , []))

  -- Easy to use do notation; i.e.;
  module RWST-do where
    infixl 1 _>>=_ _>>_
    _>>=_  : RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
    _>>=_  = RWST-bind

    _>>_   : RWST Ev Wr St A → RWST Ev Wr St B → RWST Ev Wr St B
    x >> y = x >>= λ _ → y

    return : A → RWST Ev Wr St A
    return = RWST-return

    pure : A → RWST Ev Wr St A
    pure = return

    infixr 4 _<$>_
    _<$>_ : (A → B) → RWST Ev Wr St A → RWST Ev Wr St B
    _<$>_ = RWST-map

  private
    ex₀ : RWST ℕ Wr (Lift ℓ-State ℕ) ℕ
    ex₀ = do
       x₁ ← get
       x₂ ← ask
       return (lower x₁ + x₂)
       where open RWST-do

  -- Derived Functionality

  maybeMP : RWST Ev Wr St (Maybe A) → B → (A → RWST Ev Wr St B)
          → RWST Ev Wr St B
  maybeMP ma b f = do
    x ← ma
    case x of
      λ { (just r) → f r
        ; nothing  → return b
        }
    where open RWST-do
