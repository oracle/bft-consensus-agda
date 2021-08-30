{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

module LibraBFT.ImplShared.Util.Dijkstra.EitherD where

data EitherD (E : Set) : Set → Set₁ where
  -- Primitive combinators
  EitherD-return : ∀ {A} → A → EitherD E A
  EitherD-bind   : ∀ {A B} → EitherD E A → (A → EitherD E B) → EitherD E B
  EitherD-bail   : ∀ {A} → E → EitherD E A
  -- Branching conditionals (used for creating more convenient contracts)
  EitherD-if     : ∀ {A} → Guards (EitherD E A) → EitherD E A
  EitherD-either : ∀ {A B C} → Either B C
                   → (B → EitherD E A) → (C → EitherD E A) → EitherD E A
  EitherD-maybe  : ∀ {A B} → Maybe A → EitherD E B → (A → EitherD E B) → EitherD E B

pattern LeftD  x = EitherD-bail   x
pattern RightD x = EitherD-return x

private
  variable
    E : Set
    A B C : Set

EitherD-run : EitherD E A → Either E A
EitherD-run (EitherD-return x) = Right x
EitherD-run (EitherD-bind m f)
  with EitherD-run m
... | Left x = Left x
... | Right y = EitherD-run (f y)
EitherD-run (EitherD-bail x) = Left x
EitherD-run (EitherD-if (clause (b ≔ c) gs)) =
  if toBool b then EitherD-run c else EitherD-run (EitherD-if gs)
EitherD-run (EitherD-if (otherwise≔ c)) =
  EitherD-run c
EitherD-run (EitherD-either (Left x) f₁ f₂) = EitherD-run (f₁ x)
EitherD-run (EitherD-either (Right y) f₁ f₂) = EitherD-run (f₂ y)
EitherD-run (EitherD-maybe nothing n s) = EitherD-run n
EitherD-run (EitherD-maybe (just x) n s) = EitherD-run (s x)

EitherD-Pre : (E A : Set) → Set₁
EitherD-Pre E A = Set

EitherD-Post : (E A : Set) → Set₁
EitherD-Post E A = Either E A → Set

EitherD-Post-⇒ : ∀ {E A : Set} → (P Q : EitherD-Post E A) → Set
EitherD-Post-⇒ P Q = ∀ r → P r → Q r

EitherD-PredTrans : (E A : Set) → Set₁
EitherD-PredTrans E A = EitherD-Post E A → EitherD-Pre E A

EitherD-weakestPre-bindPost : (f : A → EitherD E B) → EitherD-Post E B → EitherD-Post E A

EitherD-weakestPre : (m : EitherD E A) → EitherD-PredTrans E A
EitherD-weakestPre (EitherD-return x) P = P (Right x)
EitherD-weakestPre (EitherD-bind m f) P =
  EitherD-weakestPre m (EitherD-weakestPre-bindPost f P)
EitherD-weakestPre (EitherD-bail x) P = P (Left x)
EitherD-weakestPre (EitherD-if (clause (b ≔ c) gs)) P =
  (toBool b ≡ true → EitherD-weakestPre c P)
  × (toBool b ≡ false → EitherD-weakestPre (EitherD-if gs) P)
EitherD-weakestPre (EitherD-if (otherwise≔ x)) P =
  EitherD-weakestPre x P
EitherD-weakestPre (EitherD-either e f₁ f₂) P =
  (∀ x → e ≡ Left x → EitherD-weakestPre (f₁ x) P)
  × (∀ y → e ≡ Right y → EitherD-weakestPre (f₂ y) P)
EitherD-weakestPre (EitherD-maybe m n s) P =
  (m ≡ nothing → EitherD-weakestPre n P)
  × (∀ j → m ≡ just j → EitherD-weakestPre (s j) P)

EitherD-weakestPre-bindPost f P (Left x) =
  P (Left x)
EitherD-weakestPre-bindPost f P (Right y) =
  ∀ c → c ≡ y → EitherD-weakestPre (f c) P

EitherD-Contract : (m : EitherD E A) → Set₁
EitherD-Contract{E}{A} m =
  (P : EitherD-Post E A)
  → EitherD-weakestPre m P → P (EitherD-run m)

EitherD-contract : (m : EitherD E A) → EitherD-Contract m
EitherD-contract (EitherD-return x) P wp = wp
EitherD-contract (EitherD-bind m f) P wp
   with EitherD-contract m _ wp
...| wp'
   with EitherD-run m
... | Left x = wp'
... | Right y = EitherD-contract (f y) P (wp' y refl)
EitherD-contract (EitherD-bail x) P wp = wp
EitherD-contract{E}{A} (EitherD-if gs) P wp =
  EitherD-contract-if gs P wp
  where
  EitherD-contract-if : (gs : Guards (EitherD E A)) → EitherD-Contract (EitherD-if gs)
  EitherD-contract-if (clause (b ≔ c) gs) P wp
     with toBool b
  ... | false = EitherD-contract-if gs P (proj₂ wp refl)
  ... | true = EitherD-contract c P (proj₁ wp refl)
  EitherD-contract-if (otherwise≔ x) P wp = EitherD-contract x P wp
EitherD-contract (EitherD-either (Left x) f₁ f₂) P wp =
  EitherD-contract (f₁ x) P (proj₁ wp x refl)
EitherD-contract (EitherD-either (Right y) f₁ f₂) P wp =
  EitherD-contract (f₂ y) P (proj₂ wp y refl)
EitherD-contract (EitherD-maybe nothing f₁ f₂) P wp =
  EitherD-contract f₁ P (proj₁ wp refl)
EitherD-contract (EitherD-maybe (just x) f₁ f₂) P wp =
  EitherD-contract (f₂ x) P (proj₂ wp x refl)

postulate -- TODO-2: prove
  EitherD-⇒
    : (P Q : EitherD-Post E A)
      → (EitherD-Post-⇒ P Q)
      → ∀ m
      → EitherD-weakestPre m P
      → EitherD-weakestPre m Q
