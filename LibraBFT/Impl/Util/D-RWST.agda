{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude

-- This module defines syntax and functionality modeling an RWST monad,
-- which we use to define an implementation.
-- TODO-2: this module is independent of any particular implementation
-- and arguably belongs somewhere more general, such as next to Optics.

module LibraBFT.Impl.Util.D-RWST where

------------------
-- RWST-D Monad --
------------------

-- 'Fake' RWST monad; fake in the sense
-- we use the free monoid on the writer (aka. lists)
-- instad of requiring it to be a monoid in a separate
-- argument.
D-RWST-Raw : (Ev Wr St A : Set) → Set
D-RWST-Raw Ev Wr St A = (ev : Ev) (st : St) → (A × St × List Wr)

D-RWST-PredTrans : (Ev Wr St A : Set) → Set₁
D-RWST-PredTrans Ev Wr St A = (P : A → St → Ev → Set) (st : St) (ev : Ev) → Set

D-RWST-Contract : ∀ {Ev Wr St A} → (m : D-RWST-Raw Ev Wr St A) → (WP : D-RWST-PredTrans Ev Wr St A) → Set₁
D-RWST-Contract {Ev}{Wr}{St}{A} m WP =
  (ev : Ev) (st : St) (P : A → St → Ev → Set) → WP P st ev →
  let (r , st , _) = m ev st in P r st ev

  -- Wrap it in a type; prevents spurious evaluation and
  -- obliges us to 'run' the monad.
data D-RWST (Ev Wr St : Set) : (A : Set) → Set₂ where
  d-rwst : ∀ {A} → (m : D-RWST-Raw Ev Wr St A) (WP : D-RWST-PredTrans Ev Wr St A) → D-RWST-Contract m WP
           → D-RWST Ev Wr St A

private
  variable
    Ev Wr St : Set
    A B C    : Set

D-RWST-run : D-RWST Ev Wr St A → Ev → St → A × St × List Wr
D-RWST-run (d-rwst f _ _) = f

D-RWST-predTrans : D-RWST Ev Wr St A → D-RWST-PredTrans Ev Wr St A
D-RWST-predTrans (d-rwst _ WP _) = WP

D-RWST-contract : (m : D-RWST Ev Wr St A)
                  → D-RWST-Contract (D-RWST-run m) (D-RWST-predTrans m)
D-RWST-contract (d-rwst m WP c) = c

-- Core functionality.
D-RWST-return : A → D-RWST Ev Wr St A
D-RWST-return a =
  d-rwst (λ ev st → a , st , [])
    (λ P → P a) λ P ev st pf → pf

D-RWST-bind : D-RWST Ev Wr St A → (A → D-RWST Ev Wr St B) → D-RWST Ev Wr St B
D-RWST-bind m₁ m₂ =
  d-rwst
    (λ ev st →
     let (x₁ , st₁ , wr₁) = D-RWST-run m₁ ev st
         (x₂ , st₂ , wr₂) = D-RWST-run (m₂ x₁) ev st₁ in
     x₂ , st₂ , wr₁ ++ wr₂)
    (λ P → D-RWST-predTrans m₁ λ x → D-RWST-predTrans (m₂ x) P)
    λ ev st P pf →
      let (x₁ , st₁ , _) = D-RWST-run m₁ ev st
          m₂' = m₂ x₁ in
      D-RWST-contract m₂' ev st₁ P (D-RWST-contract m₁ ev st _ pf)

get : D-RWST Ev Wr St St
get = d-rwst (λ ev st → st , st , []) (λ P rm → P rm rm) λ P ev st pf → pf

put : St → D-RWST Ev Wr St Unit
put st = d-rwst (λ ev st₁ → unit , st , []) (λ P _ → P unit st) λ P ev st₁ pf → pf

tell : List Wr → D-RWST Ev Wr St Unit
tell wrs = d-rwst (λ ev st → unit , st , wrs) (λ P → P unit) λ P ev st pf → pf

ask : D-RWST Ev Wr St Ev
ask = d-rwst (λ ev st → ev , st , []) (λ P st ev → P ev st ev) λ P ev st pf → pf

-- Easy to use do notation; i.e.;
module D-RWST-do where
  infixl 1 _>>=_ _>>_

  _>>=_ = D-RWST-bind

  _>>_ : D-RWST Ev Wr St A → D-RWST Ev Wr St B → D-RWST Ev Wr St B
  m₁ >> m₂  = m₁ >>= λ _ → m₂

  return = D-RWST-return
  pure   = D-RWST-return

open D-RWST-do

-- Derived functionality.

-- Functorial and applicative operations.
infixl 4 _<$>_ _<*>_
_<$>_ : (A → B) → D-RWST Ev Wr St A → D-RWST Ev Wr St B
f <$> m = do
  x ← m
  return (f x)

_<*>_ : D-RWST Ev Wr St (A → B) → D-RWST Ev Wr St A → D-RWST Ev Wr St B
fs <*> m = do
   f ← fs
   x ← m
   return (f x)

tell1 : Wr → D-RWST Ev Wr St Unit
tell1 wr = tell (wr ∷ [])

act = tell1

gets : (St → A) → D-RWST Ev Wr St A
gets f = do
  x ← get
  return (f x)

modify : (St → St) → D-RWST Ev Wr St Unit
modify f = do
  x ← get
  put (f x)

-- Lens operations
use : Lens St A → D-RWST Ev Wr St A
use l = gets (_^∙ l)

setL : ∀ {A} → Lens St A → A → D-RWST Ev Wr St Unit
setL l x = modify λ st → st [ l := x ]
syntax setL l x = l ∙= x

modifyL : Lens St A → (A → A) → D-RWST Ev Wr St Unit
modifyL l f = modify (over l f)
syntax modifyL l f = l %= f

-- Combination with error monad.
ok : ∀ {B} → A → D-RWST Ev Wr St (B ⊎ A)
ok a = do return (inj₂ a)

bail : ∀ {B} → B → D-RWST Ev Wr St (B ⊎ A)
bail b = do return (inj₁ b)

-- Note: using do-notation here doesn't give the most convenient predicate transformer
infixl 4 _∙?∙_
_∙?∙_ : D-RWST Ev Wr St (C ⊎ A) → (A → D-RWST Ev Wr St (C ⊎ B)) → D-RWST Ev Wr St (C ⊎ B)
_∙?∙_ {Ev}{Wr}{St}{C}{A}{B} m f = d-rwst prog Tra contract
  where
  prog : D-RWST-Raw Ev Wr St (C ⊎ B)
  prog ev st
     with D-RWST-run m ev st
  ... | inj₁ c , st₁ , outs₁ = inj₁ c , st₁ , outs₁
  ... | inj₂ a , st₁ , outs₁ =
    let (x₂ , st₂ , outs₂) = D-RWST-run (f a) ev st₁ in
    x₂ , st₂ , outs₁ ++ outs₂

  Tra : D-RWST-PredTrans Ev Wr St (C ⊎ B)
  Tra P = D-RWST-predTrans m λ where
            (inj₂ a) → D-RWST-predTrans (f a) P
            (inj₁ c) → P (inj₁ c)

  contract : D-RWST-Contract prog Tra
  contract ev st P pf
     with D-RWST-contract m ev st _ pf
  ...| con
     with D-RWST-run m ev st
  ... | inj₁ c , st₁ , outs₁ = con
  ... | inj₂ a , st₁ , outs₁ = D-RWST-contract (f a) ev st₁ _ con

private
  test₁ : (m₁ : D-RWST Ev Wr St (C ⊎ A)) (m₂ : A → D-RWST Ev Wr St (C ⊎ B)) → D-RWST-PredTrans Ev Wr St (C ⊎ B)
  test₁ m₁ m₂ = D-RWST-predTrans (m₁ ∙?∙ m₂)

_∙^∙_ : D-RWST Ev Wr St (B ⊎ A) → (B → B) → D-RWST Ev Wr St (B ⊎ A)
_∙^∙_ {Ev}{Wr}{St}{B}{A} m f = d-rwst prog Tra contract
  where
  prog : D-RWST-Raw Ev Wr St (B ⊎ A)
  prog ev st
     with D-RWST-run m ev st
  ... | inj₂ a , st₁ , outs₁ = inj₂ a , st₁ , outs₁
  ... | inj₁ b , st₁ , outs₁ = inj₁ (f b) , st₁ , outs₁

  Tra : D-RWST-PredTrans Ev Wr St (B ⊎ A)
  Tra P = D-RWST-predTrans m λ where
            (inj₂ a) → P (inj₂ a)
            (inj₁ b) → P (inj₁ (f b))

  contract : D-RWST-Contract prog Tra
  contract ev st P pf
     with D-RWST-contract m ev st _ pf
  ...| con
     with D-RWST-run m ev st
  ... | inj₂ a , st₁ , outs₁ = con
  ... | inj₁ c , st₁ , outs₁ = con
