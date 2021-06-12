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
  -- Primitive combinators
  RWST-return : ∀ {A}   → A                                       → RWST Ev Wr St A
  RWST-bind   : ∀ {A B} → RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  RWST-get    :                                                     RWST Ev Wr St St
  RWST-put    : St                                                → RWST Ev Wr St Unit
  RWST-ask    :                                                     RWST Ev Wr St Ev
  RWST-tell   : List Wr                                           → RWST Ev Wr St Unit
  -- Branching combinators (used for creating more convenient contracts)
  RWST-if     : ∀ {A} → Guards (RWST Ev Wr St A)                  → RWST Ev Wr St A
  RWST-either : ∀ {A B C} → B ⊎ C
                → (B → RWST Ev Wr St A) → (C → RWST Ev Wr St A)   → RWST Ev Wr St A
  RWST-ebind  : ∀ {A B C}
                → RWST Ev Wr St (C ⊎ A) → (A → RWST Ev Wr St (C ⊎ B)) → RWST Ev Wr St (C ⊎ B)
  RWST-maybe  : ∀ {A B} → Maybe B
                → (RWST Ev Wr St A) → (B → RWST Ev Wr St A)       → RWST Ev Wr St A

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
RWST-run (RWST-if (clause (b ≔ c) gs)) ev st =
  if toBool b then RWST-run c ev st else RWST-run (RWST-if gs) ev st
RWST-run (RWST-if (otherwise≔ c)) ev st = RWST-run c ev st
RWST-run (RWST-either (inj₁ x) f₁ f₂) ev st = RWST-run (f₁ x) ev st
RWST-run (RWST-either (inj₂ y) f₁ f₂) ev st = RWST-run (f₂ y) ev st
RWST-run (RWST-ebind m f) ev st
   with RWST-run m ev st
...| inj₁ c , st₁ , outs₁ = inj₁ c , st₁ , outs₁
...| inj₂ a , st₁ , outs₁
   with RWST-run (f a) ev st₁
...| r , st₂ , outs₂ = r , st₂ , outs₁ ++ outs₂
RWST-run (RWST-maybe nothing f₁ f₂) ev st = RWST-run f₁ ev st
RWST-run (RWST-maybe (just x) f₁ f₂) ev st = RWST-run (f₂ x) ev st

RWST-Pre : (Ev St : Set) → Set₁
RWST-Pre Ev St = (ev : Ev) (pre : St) → Set

RWST-Post : (Wr St A : Set) → Set₁
RWST-Post Wr St A = (x : A) (post : St) (outs : List Wr) → Set

RWST-Post++ : ∀ {Wr St A} → RWST-Post Wr St A → List Wr → RWST-Post Wr St A
RWST-Post++ P outs x post outs₁ = P x post (outs ++ outs₁)

RWST-PredTrans : (Ev Wr St A : Set) → Set₁
RWST-PredTrans Ev Wr St A = RWST-Post Wr St A → RWST-Pre Ev St

RWST-weakestPre : (m : RWST Ev Wr St A) → RWST-PredTrans Ev Wr St A
RWST-weakestPre (RWST-return x) P ev pre = P x pre []
RWST-weakestPre (RWST-bind m f) P ev pre =
  RWST-weakestPre m (λ x post outs → RWST-weakestPre (f x) (RWST-Post++ P outs) ev post) ev pre
RWST-weakestPre RWST-get P ev pre = P pre pre []
RWST-weakestPre (RWST-put post) P ev pre = P unit post []
RWST-weakestPre RWST-ask P ev pre = P ev pre []
RWST-weakestPre (RWST-tell outs) P ev pre = P unit pre outs
RWST-weakestPre (RWST-if (clause (b ≔ c) gs)) P ev pre =
  (toBool b ≡ true → RWST-weakestPre c P ev pre)
  × (toBool b ≡ false → RWST-weakestPre (RWST-if gs) P ev pre)
RWST-weakestPre (RWST-if (otherwise≔ c)) P ev pre =
  RWST-weakestPre c P ev pre
RWST-weakestPre (RWST-either e f₁ f₂) P ev pre =
    (∀ x → (e ≡ inj₁ x) →
      RWST-weakestPre (f₁ x) P ev pre)
  × (∀ y → (e ≡ inj₂ y) →
       RWST-weakestPre (f₂ y) P ev pre)
RWST-weakestPre (RWST-ebind m f) P ev pre =
  (RWST-weakestPre m (λ x post outs → ∀ c → x ≡ inj₁ c → P (inj₁ c) post outs) ev pre)
  × (RWST-weakestPre m (λ x post outs → ∀ b → x ≡ inj₂ b → RWST-weakestPre (f b) (RWST-Post++ P outs) ev post) ev pre)
RWST-weakestPre (RWST-maybe m f₁ f₂) P ev pre =
  (m ≡ nothing → RWST-weakestPre f₁ P ev pre)
  × (∀ j → m ≡ just j → RWST-weakestPre (f₂ j) P ev pre)

RWST-Contract : (m : RWST Ev Wr St A) → Set₁
RWST-Contract{Ev}{Wr}{St}{A} m =
  (P : RWST-Post Wr St A)
  → (ev : Ev) (pre : St) → RWST-weakestPre m P ev pre
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
RWST-contract{Ev}{Wr}{St}{A} (RWST-if gs) P ev pre wp = RWST-contract-if gs P ev pre wp
  where
  RWST-contract-if : (gs : Guards (RWST Ev Wr St A)) → RWST-Contract (RWST-if gs)
  RWST-contract-if (clause (b ≔ c) gs) P ev pre (wp₁ , wp₂)
    with toBool b
  ...| true = RWST-contract c _ ev pre (wp₁ refl)
  ...| false = RWST-contract-if gs _ ev pre (wp₂ refl)
  RWST-contract-if (otherwise≔ x) P ev pre wp =
    RWST-contract x P ev pre wp
RWST-contract (RWST-either (inj₁ x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₁ x) _ ev pre (wp₁ x refl)
RWST-contract (RWST-either (inj₂ y) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ y) _ ev pre (wp₂ y refl)
RWST-contract (RWST-ebind m f) P ev pre (wp₁ , wp₂)
   with RWST-run m ev pre
   | inspect (λ m → RWST-run m ev pre) m
...| inj₁ x , st₁ , outs₁ | [ eq ]
   with RWST-contract m _ ev pre wp₁ x (cong proj₁ eq)
...| con rewrite sym (cong (proj₁ ∘ proj₂) eq) | sym (cong (proj₂ ∘ proj₂) eq) = con
RWST-contract (RWST-ebind m f) P ev pre (wp₁ , wp₂)
   | inj₂ y , st₁ , outs₁ | [ eq ]
   with RWST-contract m _ ev pre wp₂ y (cong proj₁ eq)
...| con₁
   with RWST-run m ev pre
RWST-contract (RWST-ebind m f) P ev pre (wp₁ , wp₂)
  | inj₂ y , .st₁' , .outs₁' | [ refl ]
  | con₁ | .(inj₂ y) , st₁' , outs₁' = RWST-contract (f y) _ ev st₁' con₁
RWST-contract (RWST-maybe nothing f₁ f₂) P ev pre (wp₁ , wp₂)
  = RWST-contract f₁ _ ev pre (wp₁ refl)
RWST-contract (RWST-maybe (just x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ x) _ ev pre (wp₂ x refl)

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

  -- Conditionals
  infix 1 ifM‖_
  ifM‖_ : Guards (RWST Ev Wr St A) → RWST Ev Wr St A
  ifM‖_ = RWST-if

  infix 0 ifM_then_else_
  ifM_then_else_ : ⦃ _ : ToBool B ⦄ → B → (c₁ c₂ : RWST Ev Wr St A) → RWST Ev Wr St A
  ifM b then c₁ else c₂ =
    ifM‖ b ≔ c₁
       ‖ otherwise≔ c₂

  infix 0 caseM⊎_of_
  caseM⊎_of_ : B ⊎ C → (B ⊎ C → RWST Ev Wr St A) → RWST Ev Wr St A
  caseM⊎ e of f = RWST-either e (f ∘ inj₁) (f ∘ inj₂)

  caseMM_of_ : Maybe B → (Maybe B → RWST Ev Wr St A) → RWST Ev Wr St A
  caseMM m of f = RWST-maybe m (f nothing) (f ∘ just)

  -- Composition with error monad
  ok : A → RWST Ev Wr St (B ⊎ A)
  ok = return ∘ inj₂

  bail : B → RWST Ev Wr St (B ⊎ A)
  bail = return ∘ inj₁

  infixl 4 _∙?∙_
  _∙?∙_ : RWST Ev Wr St (C ⊎ A) → (A → RWST Ev Wr St (C ⊎ B)) → RWST Ev Wr St (C ⊎ B)
  _∙?∙_ = RWST-ebind
  -- m ∙?∙ f = do
  --   r ← m
  --   caseM⊎ r of λ where
  --     (inj₁ c) → pure (inj₁ c)
  --     (inj₂ a) → f a

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

