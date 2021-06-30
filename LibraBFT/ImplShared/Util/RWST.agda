{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude
open import Optics.All

-- This module defines syntax and functionality modeling an RWST monad,
-- which we use to define an implementation.
-- TODO-2: this module is independent of any particular implementation
-- and arguably belongs somewhere more general, such as next to Optics.

module LibraBFT.ImplShared.Util.RWST where

data RWST (Ev Wr St : Set) : Set → Set₁ where
  -- Primitive combinators
  RWST-return : ∀ {A}   → A                                       → RWST Ev Wr St A
  RWST-bind   : ∀ {A B} → RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  RWST-gets   : ∀ {A} → (St → A)                                  → RWST Ev Wr St A
  RWST-put    : St                                                → RWST Ev Wr St Unit
  RWST-ask    :                                                     RWST Ev Wr St Ev
  RWST-tell   : List Wr                                           → RWST Ev Wr St Unit
  -- Branching combinators (used for creating more convenient contracts)
  RWST-if     : ∀ {A} → Guards (RWST Ev Wr St A)                  → RWST Ev Wr St A
  RWST-either : ∀ {A B C} → Either B C
                → (B → RWST Ev Wr St A) → (C → RWST Ev Wr St A)   → RWST Ev Wr St A
  RWST-ebind  : ∀ {A B C}
                → RWST Ev Wr St (Either C A)
                → (A → RWST Ev Wr St (Either C B))                → RWST Ev Wr St (Either C B)
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
RWST-run (RWST-gets f) ev st    = f st , st , []
RWST-run (RWST-put st) ev _     = unit , st , []
RWST-run RWST-ask ev st         = ev , st , []
RWST-run (RWST-tell outs) ev st = unit , st , outs
RWST-run (RWST-if (clause (b ≔ c) gs)) ev st =
  if toBool b then RWST-run c ev st else RWST-run (RWST-if gs) ev st
RWST-run (RWST-if (otherwise≔ c)) ev st = RWST-run c ev st
RWST-run (RWST-either (Left x) f₁ f₂) ev st = RWST-run (f₁ x) ev st
RWST-run (RWST-either (Right y) f₁ f₂) ev st = RWST-run (f₂ y) ev st
RWST-run (RWST-ebind m f) ev st
   with RWST-run m ev st
...| Left c , st₁ , outs₁ = Left c , st₁ , outs₁
...| Right a , st₁ , outs₁
   with RWST-run (f a) ev st₁
...| r , st₂ , outs₂ = r , st₂ , outs₁ ++ outs₂
RWST-run (RWST-maybe nothing f₁ f₂) ev st = RWST-run f₁ ev st
RWST-run (RWST-maybe (just x) f₁ f₂) ev st = RWST-run (f₂ x) ev st

RWST-result : RWST Ev Wr St A → Ev → St → A
RWST-result m ev st = proj₁ (RWST-run m ev st)

RWST-post : RWST Ev Wr St A → Ev → St → St
RWST-post m ev st = proj₁ (proj₂ (RWST-run m ev st))

RWST-outs : RWST Ev Wr St A → Ev → St → List Wr
RWST-outs m ev st = proj₂ (proj₂ (RWST-run m ev st))

RWST-Pre : (Ev St : Set) → Set₁
RWST-Pre Ev St = (ev : Ev) (pre : St) → Set

RWST-Post : (Wr St A : Set) → Set₁
RWST-Post Wr St A = (x : A) (post : St) (outs : List Wr) → Set

RWST-NoEffect : St → St → List Wr → Set
RWST-NoEffect pre post outs = post ≡ pre × outs ≡ []

RWST-Post++ : ∀ {Wr St A} → RWST-Post Wr St A → List Wr → RWST-Post Wr St A
RWST-Post++ P outs x post outs₁ = P x post (outs ++ outs₁)

RWST-PredTrans : (Ev Wr St A : Set) → Set₁
RWST-PredTrans Ev Wr St A = RWST-Post Wr St A → RWST-Pre Ev St

RWST-weakestPre-ebindPost : (ev : Ev) (f : A → RWST Ev Wr St (C ⊎ B)) → RWST-Post Wr St (C ⊎ B) → RWST-Post Wr St (C ⊎ A)
RWST-weakestPre-bindPost  : (ev : Ev) (f : A → RWST Ev Wr St B) → RWST-Post Wr St B → RWST-Post Wr St A

RWST-weakestPre : (m : RWST Ev Wr St A) → RWST-PredTrans Ev Wr St A
RWST-weakestPre (RWST-return x) P ev pre = P x pre []
RWST-weakestPre (RWST-bind m f) P ev pre =
  RWST-weakestPre m (RWST-weakestPre-bindPost ev f P) ev pre
RWST-weakestPre (RWST-gets f) P ev pre = P (f pre) pre []
RWST-weakestPre (RWST-put post) P ev pre = P unit post []
RWST-weakestPre RWST-ask P ev pre = P ev pre []
RWST-weakestPre (RWST-tell outs) P ev pre = P unit pre outs
RWST-weakestPre (RWST-if (clause (b ≔ c) gs)) P ev pre =
  (toBool b ≡ true → RWST-weakestPre c P ev pre)
  × (toBool b ≡ false → RWST-weakestPre (RWST-if gs) P ev pre)
RWST-weakestPre (RWST-if (otherwise≔ c)) P ev pre =
  RWST-weakestPre c P ev pre
RWST-weakestPre (RWST-either e f₁ f₂) P ev pre =
    (∀ x → (e ≡ Left x) →
      RWST-weakestPre (f₁ x) P ev pre)
  × (∀ y → (e ≡ Right y) →
       RWST-weakestPre (f₂ y) P ev pre)
RWST-weakestPre (RWST-ebind m f) P ev pre =
  RWST-weakestPre m (RWST-weakestPre-ebindPost ev f P) ev pre
  -- (RWST-weakestPre m (λ x post outs → ∀ c → x ≡ Left c → P (Left c) post outs) ev pre)
  -- × (RWST-weakestPre m (λ x post outs → ∀ b → x ≡ Right b → RWST-weakestPre (f b) (RWST-Post++ P outs) ev post) ev pre)
RWST-weakestPre (RWST-maybe m f₁ f₂) P ev pre =
  (m ≡ nothing → RWST-weakestPre f₁ P ev pre)
  × (∀ j → m ≡ just j → RWST-weakestPre (f₂ j) P ev pre)

RWST-weakestPre-ebindPost ev f Post (Left r) post outs =
  Post (Left r) post outs
RWST-weakestPre-ebindPost ev f Post (Right r) post outs =
  ∀ c → c ≡ r → RWST-weakestPre (f c) (RWST-Post++ Post outs) ev post

RWST-weakestPre-bindPost ev f Post x post outs =
  ∀ r → r ≡ x → RWST-weakestPre (f r) (RWST-Post++ Post outs) ev post

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
  RWST-contract (f x₁) _ ev st₁ (con x₁ refl)
RWST-contract (RWST-gets f) P ev pre wp = wp
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
RWST-contract (RWST-either (Left x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₁ x) _ ev pre (wp₁ x refl)
RWST-contract (RWST-either (Right y) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ y) _ ev pre (wp₂ y refl)
RWST-contract (RWST-ebind m f) P ev pre wp
   with RWST-contract m _ ev pre wp
...| con
   with RWST-run m ev pre
... | Left x , st₁ , outs₁ = con
... | Right y , st₁ , outs₁ = RWST-contract (f y) _ ev st₁ (con y refl)
RWST-contract (RWST-maybe nothing f₁ f₂) P ev pre (wp₁ , wp₂)
  = RWST-contract f₁ _ ev pre (wp₁ refl)
RWST-contract (RWST-maybe (just x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ x) _ ev pre (wp₂ x refl)

module RWST-do where

  instance
    RWST-Monad : Monad (RWST Ev Wr St)
    Monad.return RWST-Monad = RWST-return
    Monad._>>=_ RWST-Monad = RWST-bind

  pure = return

  gets : (St → A) → RWST Ev Wr St A
  gets = RWST-gets

  get : RWST Ev Wr St St
  get = gets id

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
  caseM⊎_of_ : Either B C → (Either B C → RWST Ev Wr St A) → RWST Ev Wr St A
  caseM⊎ e of f = RWST-either e (f ∘ Left) (f ∘ Right)

  caseMM_of_ : Maybe B → (Maybe B → RWST Ev Wr St A) → RWST Ev Wr St A
  caseMM m of f = RWST-maybe m (f nothing) (f ∘ just)

  -- Composition with error monad
  ok : A → RWST Ev Wr St (B ⊎ A)
  ok = return ∘ Right

  bail : B → RWST Ev Wr St (B ⊎ A)
  bail = return ∘ Left

  infixl 4 _∙?∙_
  _∙?∙_ : RWST Ev Wr St (Either C A) → (A → RWST Ev Wr St (Either C B)) → RWST Ev Wr St (Either C B)
  _∙?∙_ = RWST-ebind
  -- m ∙?∙ f = do
  --   r ← m
  --   caseM⊎ r of λ where
  --     (Left c) → pure (Left c)
  --     (Right a) → f a

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
  use f = gets (_^∙ f)

  modifyL : Lens St A → (A → A) → RWST Ev Wr St Unit
  modifyL l f = modify (over l f)
  syntax modifyL l f = l %= f

  setL : Lens St A → A → RWST Ev Wr St Unit
  setL l x = l %= const x
  syntax setL l x = l ∙= x

-- Lemmas
--------------------------------------------------
open RWST-do

RWST-impl
  : (P Q : RWST-Post Wr St A) → (∀ r st outs → P r st outs → Q r st outs)
    → ∀ m (ev : Ev) st → RWST-weakestPre m P ev st → RWST-weakestPre m Q ev st
RWST-impl P Q impl (RWST-return x) ev st pre = impl x st [] pre
RWST-impl P Q impl (RWST-bind m f) ev st pre =
  RWST-impl _ _
    (λ r₁ st₁ outs pf x x≡ →
      RWST-impl _ _
        (λ r₂ st₂ outs₁ pf₂ → impl r₂ st₂ (outs ++ outs₁) pf₂)
        (f x) ev st₁ (pf x x≡))
    m ev st pre
RWST-impl P Q impl (RWST-gets f) ev st pre = impl _ _ _ pre
RWST-impl P Q impl (RWST-put x) ev st pre = impl _ _ _ pre
RWST-impl P Q impl RWST-ask ev st pre = impl _ _ _ pre
RWST-impl P Q impl (RWST-tell x) ev st pre = impl _ _ _ pre
RWST-impl P Q impl (RWST-if (otherwise≔ x)) ev st pre = RWST-impl _ _ impl x ev st pre
RWST-impl P Q impl (RWST-if (clause (b ≔ c) cs)) ev st (pre₁ , pre₂) =
  (λ pf → RWST-impl _ _ impl c ev st (pre₁ pf))
  , λ pf → RWST-impl _ _ impl (RWST-if cs) ev st (pre₂ pf)
proj₁ (RWST-impl P Q impl (RWST-either (Left x) f₁ f₂) ev st (pre₁ , pre₂)) x₁ x₁≡ =
  RWST-impl _ _ impl (f₁ x₁) ev st (pre₁ x₁ x₁≡)
proj₂ (RWST-impl P Q impl (RWST-either (Left x) f₁ f₂) ev st (pre₁ , pre₂)) y ()
proj₁ (RWST-impl P Q impl (RWST-either (Right y) f₁ f₂) ev st (pre₁ , pre₂)) y₁ ()
proj₂ (RWST-impl P Q impl (RWST-either (Right y) f₁ f₂) ev st (pre₁ , pre₂)) y₁ y₁≡ =
  RWST-impl _ _ impl (f₂ y₁) ev st (pre₂ y₁ y₁≡)
RWST-impl P Q impl (RWST-ebind m f) ev st pre =
  RWST-impl _ _
    (λ { (Left x₁) st₁ outs x → impl _ _ _ x
       ; (Right y) st₁ outs x → λ c x₁ →
           RWST-impl _ _ (λ r st₂ outs₁ x₂ → impl r st₂ (outs ++ outs₁) x₂) (f c) ev st₁ (x c x₁)})
    m ev st pre
proj₁ (RWST-impl P Q impl (RWST-maybe x m f) ev st (pre₁ , pre₂)) ≡nothing = RWST-impl _ _ impl m ev st (pre₁ ≡nothing)
proj₂ (RWST-impl P Q impl (RWST-maybe x m f) ev st (pre₁ , pre₂)) b b≡ = RWST-impl _ _ impl (f b) ev st (pre₂ b b≡)

RWST-×
  : ∀ (P Q : RWST-Post Wr St A) m (ev : Ev) st
    → RWST-weakestPre m P ev st → RWST-weakestPre m Q ev st
    → RWST-weakestPre m (λ x post outs → P x post outs × Q x post outs) ev st
RWST-× P Q (RWST-return x) ev st p q = p , q
RWST-× P Q (RWST-bind m f) ev st p q
   with RWST-×
          (RWST-weakestPre-bindPost ev f P)
          (RWST-weakestPre-bindPost ev f Q) m ev st
          p q
...| res =
  RWST-impl _ _
    (λ r st₁ outs pf r' r'≡ →
      RWST-× (RWST-Post++ P outs) (RWST-Post++ Q outs) (f r') ev st₁ (proj₁ pf r' r'≡) (proj₂ pf r' r'≡))
    m ev st res
RWST-× P Q (RWST-gets f) ev st p q = p , q
RWST-× P Q (RWST-put x) ev st p q = p , q
RWST-× P Q RWST-ask ev st p q = p , q
RWST-× P Q (RWST-tell x) ev st p q = p , q
RWST-× P Q (RWST-if (clause (b ≔ c) gs)) ev st p q =
  (λ b≡ → RWST-× P Q c ev st (proj₁ p b≡) (proj₁ q b≡))
  , λ b≡ → RWST-× P Q (RWST-if gs) ev st (proj₂ p b≡) (proj₂ q b≡)
RWST-× P Q (RWST-if (otherwise≔ c)) ev st p q = RWST-× P Q c ev st p q
RWST-× P Q (RWST-either e c₁ c₂) ev st p q =
  (λ x x≡ → RWST-× P Q (c₁ x) ev st (proj₁ p x x≡) (proj₁ q x x≡))
  , (λ x x≡ → RWST-× P Q (c₂ x) ev st (proj₂ p x x≡) (proj₂ q x x≡))
RWST-× P Q (RWST-ebind m f) ev st p q
  with RWST-×
         (RWST-weakestPre-ebindPost ev f P)
         (RWST-weakestPre-ebindPost ev f Q) m ev st p q
...| res =
  RWST-impl _ _
    (λ where
      (Left c) st₁ outs pf → pf
      (Right a) st₁ outs (p' , q') c c≡ →
        RWST-× _ _ (f c) ev st₁ (p' c c≡) (q' c c≡))
    m ev st res
RWST-× P Q (RWST-maybe m c₁ c₂) ev st p q =
  (λ ≡nothing → RWST-× P Q c₁ ev st (proj₁ p ≡nothing) (proj₁ q ≡nothing))
  , (λ j j≡ → RWST-× P Q (c₂ j) ev st (proj₂ p j j≡) (proj₂ q j j≡))

-- Derived Functionality
maybeS-RWST : Maybe A → (RWST Ev Wr St B) → (A → RWST Ev Wr St B) → RWST Ev Wr St B
maybeS-RWST ma n j =
  caseMM ma of λ where
    nothing → n
    (just x) → j x

maybeSM : RWST Ev Wr St (Maybe A) → RWST Ev Wr St B → (A → RWST Ev Wr St B) → RWST Ev Wr St B
maybeSM mma mb f = do
  x ← mma
  caseMM x of λ where
    nothing → mb
    (just j) → f j
  where
  open RWST-do

maybeSMP : RWST Ev Wr St (Maybe A) → B → (A → RWST Ev Wr St B)
           → RWST Ev Wr St B
maybeSMP ma b f = do
  x ← ma
  caseMM x of λ where
    nothing → return b
    (just j) → f j
  where open RWST-do

_∙^∙_ : RWST Ev Wr St (Either B A) → (B → B) → RWST Ev Wr St (Either B A)
m ∙^∙ f = do
  x ← m
  case x of λ where
    (Left e) → pure (Left (f e))
    (Right r) → pure (Right r)
  where open RWST-do

