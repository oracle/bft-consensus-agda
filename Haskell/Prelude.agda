{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Prelude where

open import Level renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)

open import Data.Bool hiding (not; _≟_; _<_; _<?_; _≤_; _≤?_) public

open import Data.Unit.NonEta using (Unit; unit) public

import Relation.Binary.PropositionalEquality as PE using (_≡_; refl)

open import Function using (_∘_; id; typeOf; flip; const; _$_) public
infixl 1 _&_
_&_ = Function._|>_

import Data.Nat.DivMod as DivMod
div = DivMod._/_

open import Data.List
    hiding (map; filter; lookup; tabulate; foldl; fromMaybe; [_])
    public
foldl' = Data.List.foldl

open import Data.Maybe
   using (Maybe; just; nothing)
   renaming (_>>=_ to _Maybe->>=_)
   public
maybeHsk : ∀ {A B : Set} → B → (A → B) → Maybe A → B
maybeHsk b a→b = λ where
  nothing  → b
  (just a) → a→b a

data Ordering : Set where
  LT EQ GT : Ordering

import Relation.Binary.Definitions as BD
import Data.Nat                    as DN
import Data.Nat.Properties         as DNP
import Relation.Binary             as RB
compare : DN.ℕ → DN.ℕ → Ordering
compare m n
  with DNP.<-cmp m n
... | BD.tri< a ¬b ¬c = LT
... | BD.tri≈ ¬a b ¬c = EQ
... | BD.tri> ¬a ¬b c = GT

import Data.Product as DP
fst = DP.proj₁
snd = DP.proj₂

import Data.Sum as DS renaming ([_,_] to either)
Either : ∀ {a b} → Set a → Set b → Set (a ℓ⊔ b)
Either A B = A DS.⊎ B
pattern Left  x = DS.inj₁ x
pattern Right x = DS.inj₂ x

either = DS.either

isLeft : ∀ {a b} {A : Set a} {B : Set b} → Either A B → Bool
isLeft (Left _)  = true
isLeft (Right _) = false

isRight : ∀ {a b} {A : Set a} {B : Set b} → Either A B → Bool
isRight = Data.Bool.not ∘ isLeft

-- an approximation of Haskell's backtick notation for making infix operators; in Agda, must have
-- spaces between f and backticks
flip' : _     -- Avoids warning about definition and syntax declaration being in different scopes
flip' = flip
syntax flip' f = ` f `

------------------
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

record ToBool {a}(A : Set a) : Set a where
  field
    toBool : A → Bool
open ToBool {{ ... }} public

not : ∀ {b} {B : Set b} ⦃ _ : ToBool B ⦄ → B → Bool
not b = Data.Bool.not (toBool b)

import Relation.Nullary                as RN
import Relation.Nullary.Decidable.Core as RNDC
instance
  ToBool-Bool : ToBool Bool
  ToBool-Bool = record { toBool = id }

  ToBool-Dec : ∀{a}{A : Set a} → ToBool (RN.Dec A)
  ToBool-Dec = record { toBool = RNDC.⌊_⌋ }

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

record Functor  {ℓ₁ ℓ₂ : Level} (F : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 4 _<$>_
  field
    _<$>_ : ∀ {A B : Set ℓ₁} → (A → B) → F A → F B
  fmap = _<$>_
open Functor ⦃ ... ⦄ public

record Applicative {ℓ₁ ℓ₂ : Level} (F : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 4 _<*>_
  field
    pure  : ∀ {A : Set ℓ₁} → A → F A
    _<*>_ : ∀ {A B : Set ℓ₁} → F (A → B) → F A → F B
open Applicative ⦃ ... ⦄ public
instance
  ApplicativeFunctor : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} ⦃ _ : Applicative F ⦄ → Functor F
  Functor._<$>_ ApplicativeFunctor f xs = pure f <*> xs

record Monad {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
  infixl 1 _>>=_ _>>_
  field
    return : ∀ {A : Set ℓ₁} → A → M A
    _>>=_  : ∀ {A B : Set ℓ₁} → M A → (A → M B) → M B

  _>>_ : ∀ {A B : Set ℓ₁} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂
open Monad ⦃ ... ⦄ public
instance
  MonadApplicative : ∀ {ℓ₁ ℓ₂} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄ → Applicative M
  Applicative.pure MonadApplicative = return
  Applicative._<*>_ MonadApplicative fs xs = do
    f ← fs
    x ← xs
    return (f x)

instance
  Monad-Either : ∀ {ℓ}{C : Set ℓ} → Monad{ℓ}{ℓ} (Either C)
  Monad.return (Monad-Either{ℓ}{C}) = DS.inj₂
  Monad._>>=_ (Monad-Either{ℓ}{C}) = DS.either (const ∘ DS.inj₁) _&_

  Monad-Maybe : ∀ {ℓ} → Monad {ℓ} {ℓ} Maybe
  Monad.return (Monad-Maybe{ℓ}) = just
  Monad._>>=_  (Monad-Maybe{ℓ}) = _Maybe->>=_

  Monad-List : ∀ {ℓ} → Monad {ℓ}{ℓ} List
  Monad.return Monad-List x   = x ∷ []
  Monad._>>=_  Monad-List x f = concat (Data.List.map f x)

fromMaybeM : ∀ {ℓ} {A : Set} {m : Set → Set ℓ} ⦃ _ : Monad m ⦄ → m A → m (Maybe A) → m A
fromMaybeM ma mma = do
  mma >>= λ where
    nothing  → ma
    (just a) → pure a

forM_ : ∀ {ℓ} {A B : Set} {M : Set → Set ℓ} ⦃ _ : Monad M ⦄ → List A → (A → M B) → M Unit
forM_      []  _ = return unit
forM_ (x ∷ xs) f = f x >> forM_ xs f

-- NOTE: because 'forM_' is defined above, it is necessary to
-- call 'forM' with parenthesis (e.g., recursive call in definition)
-- to disambiguate it for the Agda parser.
forM  : ∀ {ℓ} {A B : Set} {M : Set → Set ℓ} ⦃ _ : Monad M ⦄ → List A → (A → M B) → M (List B)
forM      []  _ = return []
forM (x ∷ xs) f = do
  fx  ← f x
  fxs ← (forM) xs f
  return (fx ∷ fxs)

foldrM : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄
       → (A → B → M B) → B → List A → M B
foldrM _ b      []  = return b
foldrM f b (a ∷ as) = foldrM f b as >>= f a

foldlM : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {M : Set ℓ₁ → Set ℓ₂} ⦃ _ : Monad M ⦄
       → (B → A → M B) → B → List A → M B
foldlM _ z      []  = pure z
foldlM f z (x ∷ xs) = do
  z' ← f z x
  foldlM f z' xs

foldM = foldlM

foldM_ : {A B : Set} {M : Set → Set} ⦃ _ : Monad M ⦄ → (B → A → M B) → B → List A → M Unit
foldM_ f a xs = foldlM f a xs >> pure unit

record Eq {a} (A : Set a) : Set a where
  infix 4 _≟_ _==_ _/=_
  field
    _≟_ : (a b : A) → RN.Dec (a PE.≡ b)

  _==_   : A → A → Bool
  a == b = toBool $ a ≟ b

  _/=_ : A → A → Bool
  a /= b = not (a == b)
open Eq ⦃ ... ⦄ public

import Data.List.Relation.Unary.Any as Any using (any)

elem : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → A → List A → Bool
elem x = toBool ∘ Any.any (x ≟_)

instance
  Eq-Nat : Eq DN.ℕ
  Eq._≟_ Eq-Nat = DN._≟_

  Eq-Maybe : ∀ {a} {A : Set a} ⦃ _ : Eq A ⦄ → Eq (Maybe A)
  Eq._≟_ Eq-Maybe  nothing  nothing = RN.yes PE.refl
  Eq._≟_ Eq-Maybe (just _)  nothing = RN.no λ ()
  Eq._≟_ Eq-Maybe  nothing (just _) = RN.no λ ()
  Eq._≟_ Eq-Maybe (just a) (just b)
     with a ≟ b
  ... | RN.no  proof   = RN.no λ where PE.refl → proof PE.refl
  ... | RN.yes PE.refl = RN.yes PE.refl

infixl 9 _!?_
_!?_ : {A : Set} → List A → DN.ℕ → Maybe A
[]       !?         _   = nothing
(x ∷ _ ) !?         0   = just x
(_ ∷ xs) !? (DN.suc n)  = xs !? n

find' : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe B
find' f      []  = nothing
find' f (a ∷ xs) = Data.Maybe.maybe′ f (find' f xs) (just a)
