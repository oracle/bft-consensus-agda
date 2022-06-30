{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Prelude where

open import Haskell.Modules.Either public
open import Haskell.Modules.Eq public
open import Haskell.Modules.FunctorApplicativeMonad public
open import Haskell.Modules.ToBool public
------------------------------------------------------------------------------
open import Level
  renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
open import Data.Bool
  hiding (not; _≟_; _<_; _<?_; _≤_; _≤?_)
  public
open import Data.Empty
  renaming (⊥ to Void)
  public
open import Data.List
  hiding (map; filter; lookup; tabulate; foldl; fromMaybe; [_])
  public
import      Data.Nat            as DN
import      Data.Nat.DivMod     as DivMod
import      Data.Nat.Properties as DNP
open import Data.Maybe
  using (Maybe; just; nothing)
  renaming (_>>=_ to _Maybe->>=_)
  public
import      Data.Product as DP
open import Data.Unit.NonEta
  using (Unit; unit)
  public
open import Function
  using (_∘_; id; typeOf; flip; const; _$_)
  public
import      Relation.Binary.PropositionalEquality as PE
  using (_≡_; refl)
import      Relation.Binary.Definitions as BD
import      Relation.Binary             as RB

------------------------------------------------------------------------------

infixl 1 _&_
_&_ = Function._|>_

-- An approximation of Haskell's backtick notation for making infix operators.
-- In Agda, there must be spaces between f and backticks
flip' : _  -- Avoids warning about definition and syntax declaration being in different scopes.
flip' = flip
syntax flip' f = ` f `

------------------------------------------------------------------------------
-- Guard Syntax --
--
-- Example Usage:
--
-- > f : ℕ → ℕ
-- > f x = grd‖ x ≟ℕ 10  ≔ 12
-- >          ‖ otherwise≔ 40 + 2
--
--
-- > g : ℕ ⊎ ℕ → ℕ
-- > g x = case x of λ
-- >     { (inj₁ x) → grd‖ x ≤? 10  ≔ 2 * x
-- >                     ‖ otherwise≔ 42
-- >     ; (inj₂ y) → y
-- >     }
--
-- To type: ‖  -->  \Vert
--          ≔  -->  \:=

infix 3 _≔_
data GuardClause {a}{b}(A : Set a) : Set (a ℓ⊔ ℓ+1 b) where
  _≔_ : {B : Set b}{{ bb : ToBool B }} → B → A → GuardClause A

infix 3 otherwise≔_
data Guards {a}{b}(A : Set a) : Set (a ℓ⊔ ℓ+1 b) where
 otherwise≔_ : A → Guards A
 clause     : GuardClause{a}{b} A → Guards{a}{b} A → Guards A

infixr 2 _‖_
_‖_ : ∀{a}{b}{A : Set a} → GuardClause{a}{b} A → Guards A → Guards A
_‖_ = clause

infix 1 grd‖_
grd‖_ : ∀{a}{b}{A : Set a} → Guards{a}{b} A → A
grd‖_ (otherwise≔ a) = a
grd‖_ (clause (b ≔ a) g)  = if toBool b then a else (grd‖ g)

lengthGuards : ∀ {a}{b}{A : Set a} → Guards{a}{b} A → DN.ℕ
lengthGuards (otherwise≔ x) = 1
lengthGuards (clause x x₁) = 1 DN.+ lengthGuards x₁

------------------------------------------------------------------------------
-- List

infixl 9 _!?_
_!?_ : {A : Set} → List A → DN.ℕ → Maybe A
[]       !?         _   = nothing
(x ∷ _ ) !?         0   = just x
(_ ∷ xs) !? (DN.suc n)  = xs !? n

find' : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe B
find' f      []  = nothing
find' f (a ∷ xs) = Data.Maybe.maybe′ f (find' f xs) (just a)

foldl' = Data.List.foldl

------------------------------------------------------------------------------
-- Maybe

maybe : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → B → (A → B) → Maybe A → B
maybe b a→b = Data.Maybe.maybe′ a→b b

------------------------------------------------------------------------------
-- Nat

div = DivMod._/_

data Ordering : Set where
  LT EQ GT : Ordering

compare : DN.ℕ → DN.ℕ → Ordering
compare m n
  with DNP.<-cmp m n
... | BD.tri< a ¬b ¬c = LT
... | BD.tri≈ ¬a b ¬c = EQ
... | BD.tri> ¬a ¬b c = GT

------------------------------------------------------------------------------
-- Product

fst = DP.proj₁
snd = DP.proj₂

------------------------------------------------------------------------------
-- Monad

foldlM : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄
       → (B → A → M B) → B → List A → M B
foldlM _ z      []  = pure z
foldlM f z (x ∷ xs) = do
  z' ← f z x
  foldlM f z' xs

foldrM : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄
       → (A → B → M B) → B → List A → M B
foldrM _ b      []  = return b
foldrM f b (a ∷ as) = foldrM f b as >>= f a

foldM = foldlM

foldM_ : {A B : Set} {M : Set → Set} ⦃ _ : Monad M ⦄ → (B → A → M B) → B → List A → M Unit
foldM_ f a xs = foldlM f a xs >> pure unit

fromMaybeM : ∀ {ℓ} {A : Set} {m : Set → Set ℓ} ⦃ _ : Monad m ⦄ → m A → m (Maybe A) → m A
fromMaybeM ma mma = do
  mma >>= λ where
    nothing  → ma
    (just a) → pure a

-- NOTE: because 'forM_' is defined above, it is necessary to
-- call 'forM' with parenthesis (e.g., recursive call in definition)
-- to disambiguate it for the Agda parser.
forM  : ∀ {ℓ} {A B : Set} {M : Set → Set ℓ} ⦃ _ : Monad M ⦄ → List A → (A → M B) → M (List B)
forM      []  _ = return []
forM (x ∷ xs) f = do
  fx  ← f x
  fxs ← (forM) xs f
  return (fx ∷ fxs)

forM_ : ∀ {ℓ} {A B : Set} {M : Set → Set ℓ} ⦃ _ : Monad M ⦄ → List A → (A → M B) → M Unit
forM_      []  _ = return unit
forM_ (x ∷ xs) f = f x >> forM_ xs f

