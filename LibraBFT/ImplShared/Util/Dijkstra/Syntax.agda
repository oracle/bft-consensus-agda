{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Util.Dijkstra.RWST
open import LibraBFT.ImplShared.Util.Dijkstra.Error
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.ImplShared.Util.Dijkstra.Syntax where

{-
Within a "Dijkstra-fied" monad `M`, `if` and `ifD` are semantically interchangeable.

The difference is in how proof obligations are generated
- with the *D variants generating new weakestPre obligations for each case.

In some cases, this is helpful for structuring proofs, while in other cases it is
unnecessary and introduces more structure to the proof without adding any benefit.

A rule of thumb is that, if the "scrutinee" (whatever we are doing case analysis on,
i.e., the first argument) is the value provided via >>= (bind) by a previous code block,
then we already have a weakestPre proof obligation, so introducing additional ones via the
*D variants only creates more work and provides no additional benefit.
-}

record MonadIfD {ℓ₁ ℓ₂ ℓ₃ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁ ℓ⊔ ℓ+1 ℓ₃) where
  infix 1 ifD‖_
  field
    ⦃ monad ⦄ : Monad M
    ifD‖_ : ∀ {A : Set ℓ₁} → Guards{ℓ₂}{ℓ₃} (M A) → M A

open MonadIfD ⦃ ... ⦄ public

module _ {ℓ₁ ℓ₂ ℓ₃} {M : Set ℓ₁ → Set ℓ₂} where

  private
    variable
      A : Set ℓ₁
      B : Set ℓ₃

  infix 0 ifD_then_else_
  ifD_then_else_ : ⦃ _ : MonadIfD{ℓ₃ = ℓ₃} M ⦄ ⦃ _ : ToBool B ⦄ → B → (c₁ c₂ : M A) → M A
  ifD b then c₁ else c₂ =
    ifD‖ b ≔ c₁
       ‖ otherwise≔ c₂

whenD : ∀ {ℓ₂ ℓ₃} {M : Set → Set ℓ₂} {B : Set ℓ₃} ⦃ _ : MonadIfD{ℓ0}{ℓ₂}{ℓ₃} M ⦄ ⦃ _ : ToBool B ⦄ → B → M Unit → M Unit
whenD b f = ifD b then f else pure unit

module _ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} where
  private
    variable A B : Set ℓ₁

  ifMD : ⦃ mi : MonadIfD{ℓ₃ = ℓ₁} M ⦄ ⦃ _ : ToBool B ⦄ → M B → (c₁ c₂ : M A) → M A
  ifMD{B = B} ⦃ mi ⦄ m c₁ c₂ = do
    x ← m
    ifD x then c₁ else c₂

record MonadMaybeD {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  field
    ⦃ monad ⦄ : Monad M
    maybeSD : ∀ {A B : Set ℓ₁} → Maybe A → M B → (A → M B) → M B

open MonadMaybeD ⦃ ... ⦄ public

infix 0 caseMD_of_
caseMD_of_ : ∀ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : MonadMaybeD M ⦄ {A B : Set ℓ₁} → Maybe A → (Maybe A → M B) → M B
caseMD m of f = maybeSD m (f nothing) (f ∘ just)

record MonadEitherD {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  field
    ⦃ monad ⦄ : Monad M
    eitherSD : ∀ {E A B : Set ℓ₁} → Either E A → (E → M B) → (A → M B) → M B

open MonadEitherD ⦃ ... ⦄ public

infix 0 case⊎D_of_
case⊎D_of_ : ∀ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : MonadEitherD M ⦄ {E A B : Set ℓ₁} → Either E A → (Either E A → M B) → M B
case⊎D e of f = eitherSD e (f ∘ Left) (f ∘ Right)

-- Conditionals


-- infix 1 ifM‖_
-- ifM‖_ : Guards (RWST Ev Wr St A) → RWST Ev Wr St A
-- ifM‖_ = RWST-if

-- infix 0 if-RWST_then_else_
-- if-RWST_then_else_ : ⦃ _ : ToBool B ⦄ → B → (c₁ c₂ : RWST Ev Wr St A) → RWST Ev Wr St A
-- if-RWST b then c₁ else c₂ =
--   ifM‖ b ≔ c₁
--      ‖ otherwise≔ c₂

-- -- This is like the Haskell version, except Haskell's works for any monad (not just RWST).
-- ifM : ⦃ _ : ToBool B ⦄ → RWST Ev Wr St B → (c₁ c₂ : RWST Ev Wr St A) → RWST Ev Wr St A
-- ifM mb c₁ c₂ = do
--   x ← mb
--   if-RWST x then c₁ else c₂

-- infix 0 caseM⊎_of_ caseMM_of_
-- caseM⊎_of_ : Either B C → (Either B C → RWST Ev Wr St A) → RWST Ev Wr St A
-- caseM⊎ e of f = RWST-either e (f ∘ Left) (f ∘ Right)

-- caseMM_of_ : Maybe B → (Maybe B → RWST Ev Wr St A) → RWST Ev Wr St A
-- caseMM m of f = RWST-maybe m (f nothing) (f ∘ just)

-- eitherS-RWST : ∀ {A B C} → Either B C
--                → (B → RWST Ev Wr St A) → (C → RWST Ev Wr St A)   → RWST Ev Wr St A
-- eitherS-RWST = RWST-either

-- when : ∀ {ℓ} {B : Set ℓ} ⦃ _ : ToBool B ⦄ → B → RWST Ev Wr St Unit → RWST Ev Wr St Unit
-- when b f = if-RWST toBool b then f else pure unit

-- when-RWST : ⦃ _ : ToBool B ⦄ → B → (c : RWST Ev Wr St Unit) → RWST Ev Wr St Unit
-- when-RWST b c = if-RWST b then c else pure unit

-- -- Composition with error monad
-- ok : A → RWST Ev Wr St (B ⊎ A)
-- ok = pure ∘ Right

-- bail : B → RWST Ev Wr St (B ⊎ A)
-- bail = pure ∘ Left

-- infixl 4 _∙?∙_
-- _∙?∙_ : RWST Ev Wr St (Either C A) → (A → RWST Ev Wr St (Either C B)) → RWST Ev Wr St (Either C B)
-- _∙?∙_ = RWST-ebind

-- -- Composition/use with partiality monad
-- maybeS-RWST : Maybe A → (RWST Ev Wr St B) → (A → RWST Ev Wr St B) → RWST Ev Wr St B
-- maybeS-RWST ma n j =
--   caseMM ma of λ where
--     nothing  → n
--     (just x) → j x

-- maybeSM : RWST Ev Wr St (Maybe A) → RWST Ev Wr St B → (A → RWST Ev Wr St B) → RWST Ev Wr St B
-- maybeSM mma mb f = do
--   x ← mma
--   caseMM x of λ where
--     nothing  → mb
--     (just j) → f j
--   where

-- maybeSMP-RWST : RWST Ev Wr St (Maybe A) → B → (A → RWST Ev Wr St B)
--               → RWST Ev Wr St B
-- maybeSMP-RWST ma b f = do
--   x ← ma
--   caseMM x of λ where
--     nothing  → pure b
--     (just j) → f j

-- infixl 4 _∙^∙_
-- _∙^∙_ : RWST Ev Wr St (Either B A) → (B → B) → RWST Ev Wr St (Either B A)
-- m ∙^∙ f = do
--   x ← m
--   either (bail ∘ f) ok x

-- RWST-weakestPre-∙^∙Post : (ev : Ev) (e : C → C) → RWST-Post Wr St (C ⊎ A) → RWST-Post Wr St (C ⊎ A)
-- RWST-weakestPre-∙^∙Post ev e Post =
--   RWST-weakestPre-bindPost ev (either (bail ∘ e) ok) Post

-- -- Lens functionality
-- --
-- -- If we make RWST work for different level State types, we will break use and
-- -- modify because Lens does not support different levels, we define use and
-- -- modify' here for RoundManager. We are ok as long as we can keep
-- -- RoundManager in Set. If we ever need to make RoundManager at some higher
-- -- Level, we will have to consider making Lens level-agnostic. Preliminary
-- -- exploration by @cwjnkins showed this to be somewhat painful in particular
-- -- around composition, so we are not pursuing it for now.
-- use : Lens St A → RWST Ev Wr St A
-- use f = gets (_^∙ f)

-- modifyL : Lens St A → (A → A) → RWST Ev Wr St Unit
-- modifyL l f = modify (over l f)
-- syntax modifyL l f = l %= f

-- setL : Lens St A → A → RWST Ev Wr St Unit
-- setL l x = l %= const x
-- syntax setL l x = l ∙= x

-- setL? : Lens St (Maybe A) → A → RWST Ev Wr St Unit
-- setL? l x = l ∙= just x
-- syntax setL? l x = l ?= x
