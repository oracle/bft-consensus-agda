{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

module LibraBFT.ImplShared.Util.Dijkstra.Error where

data Error (E : Set) : Set → Set₁ where
  -- Primitive combinators
  Error-return : ∀ {A} → A → Error E A
  Error-bind   : ∀ {A B} → Error E A → (A → Error E B) → Error E B
  Error-bail   : ∀ {A} → E → Error E A
  -- Branching conditionals (used for creating more convenient contracts)
  Error-if     : ∀ {A} → Guards (Error E A) → Error E A
  Error-maybe  : ∀ {A B} → Maybe A → Error E B → (A → Error E B) → Error E B

private
  variable
    E : Set
    A B C : Set

Error-run : Error E A → Either E A
Error-run (Error-return x) = Right x
Error-run (Error-bind m f)
  with Error-run m
... | Left x = Left x
... | Right y = Error-run (f y)
Error-run (Error-bail x) = Left x
Error-run (Error-if (clause (b ≔ c) gs)) =
  if toBool b then Error-run c else Error-run (Error-if gs)
Error-run (Error-if (otherwise≔ c)) =
  Error-run c
Error-run (Error-maybe nothing n s) = Error-run n
Error-run (Error-maybe (just x) n s) = Error-run (s x)

Error-Pre : (E A : Set) → Set₁
Error-Pre E A = Set

Error-Post : (E A : Set) → Set₁
Error-Post E A = Either E A → Set

Error-PredTrans : (E A : Set) → Set₁
Error-PredTrans E A = Error-Post E A → Error-Pre E A

Error-weakestPre-bindPost : (f : A → Error E B) → Error-Post E B → Error-Post E A

Error-weakestPre : (m : Error E A) → Error-PredTrans E A
Error-weakestPre (Error-return x) P = P (Right x)
Error-weakestPre (Error-bind m f) P =
  Error-weakestPre m (Error-weakestPre-bindPost f P)
Error-weakestPre (Error-bail x) P = P (Left x)
Error-weakestPre (Error-if (clause (b ≔ c) gs)) P =
  (toBool b ≡ true → Error-weakestPre c P)
  × (toBool b ≡ false → Error-weakestPre (Error-if gs) P)
Error-weakestPre (Error-if (otherwise≔ x)) P =
  Error-weakestPre x P
Error-weakestPre (Error-maybe m n s) P =
  (m ≡ nothing → Error-weakestPre n P)
  × (∀ j → m ≡ just j → Error-weakestPre (s j) P)

Error-weakestPre-bindPost f P (Left x) =
  P (Left x)
Error-weakestPre-bindPost f P (Right y) =
  ∀ c → c ≡ y → Error-weakestPre (f c) P

Error-Contract : (m : Error E A) → Set₁
Error-Contract{E}{A} m =
  (P : Error-Post E A)
  → Error-weakestPre m P → P (Error-run m)

Error-contract : (m : Error E A) → Error-Contract m
Error-contract (Error-return x) P wp = wp
Error-contract (Error-bind m f) P wp
   with Error-contract m _ wp
...| wp'
   with Error-run m
... | Left x = wp'
... | Right y = Error-contract (f y) P (wp' y refl)
Error-contract (Error-bail x) P wp = wp
Error-contract{E}{A} (Error-if gs) P wp =
  Error-contract-if gs P wp
  where
  Error-contract-if : (gs : Guards (Error E A)) → Error-Contract (Error-if gs)
  Error-contract-if (clause (b ≔ c) gs) P wp
     with toBool b
  ... | false = Error-contract-if gs P (proj₂ wp refl)
  ... | true = Error-contract c P (proj₁ wp refl)
  Error-contract-if (otherwise≔ x) P wp = Error-contract x P wp
Error-contract (Error-maybe nothing f₁ f₂) P wp =
  Error-contract f₁ P (proj₁ wp refl)
Error-contract (Error-maybe (just x) f₁ f₂) P wp =
  Error-contract (f₂ x) P (proj₂ wp x refl)
