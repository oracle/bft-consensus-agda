{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

module LibraBFT.ImplShared.Util.Error where


data Error (E : Set) : Set → Set₁ where
  Error-return : ∀ {A} → A → Error E A
  Error-bind   : ∀ {A B} → Error E A → (A → Error E B) → Error E B
  Error-bail   : ∀ {A} → E → Error E A

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
