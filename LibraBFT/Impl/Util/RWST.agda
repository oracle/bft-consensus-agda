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

module LibraBFT.Impl.Util.RWST where

data RWST (Ev Wr St : Set) : Set → Set₁ where
  RWST-return : ∀ {A}   → A                                       → RWST Ev Wr St A
  RWST-bind   : ∀ {A B} → RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  RWST-get    :                                                     RWST Ev Wr St St
  RWST-put    : St                                                → RWST Ev Wr St Unit
  RWST-ask    :                                                     RWST Ev Wr St Ev
  RWST-tell   : List Wr                                           → RWST Ev Wr St Unit

private
  variable
    Ev Wr St : Set
    A B C    : Set

RWST-run : RWST Ev Wr St A → Ev → St → A × St × List Wr
RWST-run (RWST-return x) ev st  = x , st , []
RWST-run (RWST-bind m f) ev st
   with RWST-run m ev st
...| x₁ , st₁ , outs₁
   with RWST-run (f x₁) ev st₁
...| x₂ , st₂ , outs₂           = x₂ , st₂ , outs₁ ++ outs₂
RWST-run RWST-get ev st         = st , st , []
RWST-run (RWST-put st) ev _     = unit , st , []
RWST-run RWST-ask ev st         = ev , st , []
RWST-run (RWST-tell outs) ev st = unit , st , outs

RWST-Pre : (Ev St : Set) → Set₁
RWST-Pre Ev St = (ev : Ev) (pre : St) → Set

RWST-Post : (Wr St A : Set) → Set₁
RWST-Post Wr St A = (x : A) (post : St) (outs : List Wr) → Set

RWST-Post++ : ∀ {Wr St A} → RWST-Post Wr St A → List Wr → RWST-Post Wr St A
RWST-Post++ P outs x post outs₁ = P x post (outs ++ outs₁)

RWST-PredTrans : (Ev Wr St A : Set) → Set₁
RWST-PredTrans Ev Wr St A = RWST-Post Wr St A → RWST-Pre Ev St

RWST-predTrans : (m : RWST Ev Wr St A) → RWST-PredTrans Ev Wr St A
RWST-predTrans (RWST-return x) P ev pre = P x pre []
RWST-predTrans (RWST-bind m f) P ev pre =
  RWST-predTrans m (λ x post outs → RWST-predTrans (f x) (RWST-Post++ P outs) ev post) ev pre
RWST-predTrans RWST-get P ev pre = P pre pre []
RWST-predTrans (RWST-put post) P ev pre = P unit post []
RWST-predTrans RWST-ask P ev pre = P ev pre []
RWST-predTrans (RWST-tell outs) P ev pre = P unit pre outs

RWST-Contract : (m : RWST Ev Wr St A) → Set₁
RWST-Contract{Ev}{Wr}{St}{A} m =
  (P : RWST-Post Wr St A)
  → (ev : Ev) (pre : St) → RWST-predTrans m P ev pre
  → let (x , post , outs) = RWST-run m ev pre in
    P x post outs

RWST-contract : (m : RWST Ev Wr St A) → RWST-Contract m
RWST-contract (RWST-return x₁) P ev pre wp = wp
RWST-contract (RWST-bind m f) P ev pre wp
   with RWST-contract m _ ev pre wp
...| con
   with RWST-run m ev pre
...| x₁ , st₁ , outs₁ =
  RWST-contract (f x₁) _ ev st₁ con
RWST-contract RWST-get P ev pre wp = wp
RWST-contract (RWST-put x₁) P ev pre wp = wp
RWST-contract RWST-ask P ev pre wp = wp
RWST-contract (RWST-tell x₁) P ev pre wp = wp

module RWST-do where
  infixl 1 _>>=_ _>>_
  _>>=_ : RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  _>>=_ = RWST-bind

  _>>_ : RWST Ev Wr St A → RWST Ev Wr St B → RWST Ev Wr St B
  x >> y = x >>= const y

  return : A → RWST Ev Wr St A
  return = RWST-return

  pure = return

  get : RWST Ev Wr St St
  get = RWST-get

  gets : (St → A) → RWST Ev Wr St A
  gets f = do
    st ← get
    return (f st)

  put : St → RWST Ev Wr St Unit
  put = RWST-put

  modify : (St → St) → RWST Ev Wr St Unit
  modify f = do
    st ← get
    put (f st)

  ask : RWST Ev Wr St Ev
  ask = RWST-ask

  tell : List Wr → RWST Ev Wr St Unit
  tell = RWST-tell

  tell1 : Wr → RWST Ev Wr St Unit
  tell1 x = tell (x ∷ [])

  act = tell1

  -- Composition with error monad
  ok : A → RWST Ev Wr St (B ⊎ A)
  ok = return ∘ inj₂

  bail : B → RWST Ev Wr St (B ⊎ A)
  bail = return ∘ inj₁

  infixl 4 _∙?∙_
  _∙?∙_ : RWST Ev Wr St (C ⊎ A) → (A → RWST Ev Wr St (C ⊎ B)) → RWST Ev Wr St (C ⊎ B)
  m ∙?∙ f = do
    r ← m
    case r of λ where
      (inj₁ c) → pure (inj₁ c)
      (inj₂ a) → f a

  -- Functorial functionality.
  infixl 4 _<$>_ _<*>_
  _<$>_ : (A → B) → RWST Ev Wr St A → RWST Ev Wr St B
  f <$> m = do
    x ← m
    pure (f x)

  _<*>_ : RWST Ev Wr St (A → B) → RWST Ev Wr St A → RWST Ev Wr St B
  fs <*> m = do
    f ← fs
    x ← m
    pure (f x)

  -- Lens functionality
  --
  -- If we make RWST work for different level State types, we will break use and
  -- modify because Lens does not support different levels, we define use and
  -- modify' here for RoundManager. We are ok as long as we can keep
  -- RoundManager in Set. If we ever need to make RoundManager at some higher
  -- Level, we will have to consider making Lens level-agnostic. Preliminary
  -- exploration by @cwjnkins showed this to be somewhat painful in particular
  -- around composition, so we are not pursuing it for now.
  use : Lens St A → RWST Ev Wr St A
  use f = do
    st ← get
    pure (st ^∙ f)

  modifyL : Lens St A → (A → A) → RWST Ev Wr St Unit
  modifyL l f = modify (over l f)
  syntax modifyL l f = l %= f

  setL : Lens St A → A → RWST Ev Wr St Unit
  setL l x = l %= const x
  syntax setL l x = l ∙= x

{-
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

_∙^∙_ : RWST Ev Wr St (B ⊎ A) → (B → B) → RWST Ev Wr St (B ⊎ A)
  m ∙^∙ f = do
    x ← m
    case x of λ where
      (inj₁ e) → pure (inj₁ (f e))
      (inj₂ r) → pure (inj₂ r)
    where open RWST-do
-}
