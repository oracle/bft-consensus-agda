{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.EitherD where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Haskell.Prelude

data EitherD (E : Set) : Set → Set₁ where
  -- Primitive combinators
  EitherD-return : ∀ {A} → A → EitherD E A
  EitherD-bind   : ∀ {A B} → EitherD E A → (A → EitherD E B) → EitherD E B
  EitherD-bail   : ∀ {A} → E → EitherD E A
  -- Branching conditionals (used for creating more convenient contracts)
  EitherD-if     : ∀ {A} → Guards (EitherD E A) → EitherD E A
  EitherD-either : ∀ {A B C}
                   → (B → EitherD E A) → (C → EitherD E A) → Either B C → EitherD E A
  EitherD-maybe  : ∀ {A B} → EitherD E B → (A → EitherD E B) → Maybe A → EitherD E B

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
EitherD-run (EitherD-either f₁ f₂ (Left x))  = EitherD-run (f₁ x)
EitherD-run (EitherD-either f₁ f₂ (Right y)) = EitherD-run (f₂ y)
EitherD-run (EitherD-maybe n s nothing ) = EitherD-run n
EitherD-run (EitherD-maybe n s (just x)) = EitherD-run (s x)

EitherD-Pre : (E A : Set) → Set₁
EitherD-Pre E A = Set

EitherD-Post : (E A : Set) → Set₁
EitherD-Post E A = Either E A → Set

EitherD-Post-⇒ : ∀ {E} {A} → (P Q : EitherD-Post E A) → Set
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
EitherD-weakestPre (EitherD-either f₁ f₂ e) P =
  (∀ x → e ≡ Left x → EitherD-weakestPre (f₁ x) P)
  × (∀ y → e ≡ Right y → EitherD-weakestPre (f₂ y) P)
EitherD-weakestPre (EitherD-maybe n s m) P =
  (m ≡ nothing → EitherD-weakestPre n P)
  × (∀ j → m ≡ just j → EitherD-weakestPre (s j) P)

EitherD-weakestPre-bindPost f P (Left x) =
  P (Left x)
EitherD-weakestPre-bindPost f P (Right y) =
  ∀ c → c ≡ y → EitherD-weakestPre (f c) P

-- For any post contition P and EitherD program m, if
-- EitherD-weakestPre m P holds, then P holds of the result
-- of running m.
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
EitherD-contract (EitherD-either f₁ f₂ (Left x)) P wp =
  EitherD-contract (f₁ x) P (proj₁ wp x refl)
EitherD-contract (EitherD-either f₁ f₂ (Right y)) P wp =
  EitherD-contract (f₂ y) P (proj₂ wp y refl)
EitherD-contract (EitherD-maybe f₁ f₂ nothing) P wp =
  EitherD-contract f₁ P (proj₁ wp refl)
EitherD-contract (EitherD-maybe f₁ f₂ (just x)) P wp =
  EitherD-contract (f₂ x) P (proj₂ wp x refl)

-- If P holds of the result of running m, then EitherD-weakestPre m P
-- holds.  This shows that EitherD-weakestPre really does compute the
-- weakest precondition, which is interesting and comforting, but not
-- important for the correctness of results proved using it.
-- Chris said: EitherD-weakestPre m P is a terminal object in the
-- (provability) category of preconditions for P
-- Mark agreed :-)
Post⇒wp : (m : EitherD E A) → Set₁
Post⇒wp {E}{A} m =
  (P : EitherD-Post E A)
  → P (EitherD-run m)
  → EitherD-weakestPre m P

EitherD-wp-is-weakest : (m : EitherD E A) → Post⇒wp m
EitherD-wp-is-weakest (RightD _) P = id
EitherD-wp-is-weakest (EitherD-bind m f) P Pr
  with EitherD-wp-is-weakest m
...| rec
  with EitherD-run m
... | Left  _ = rec _ Pr
... | Right y =  rec _ λ where c refl → EitherD-wp-is-weakest (f y) _ Pr
EitherD-wp-is-weakest (LeftD _) _ = id
EitherD-wp-is-weakest (EitherD-if gs) P Prun =
  EitherD-contract-if gs P Prun
  where
  EitherD-contract-if : (gs : Guards (EitherD E A)) → Post⇒wp (EitherD-if gs)
  EitherD-contract-if (otherwise≔ m) P Prun = EitherD-wp-is-weakest m P Prun
  EitherD-contract-if (clause (b ≔ c) gs') P Prun
    with toBool b
  ... | false = (λ ()) , (λ _ → EitherD-contract-if gs' _ Prun)
  ... | true  = (λ _ → EitherD-wp-is-weakest c P Prun) , (λ ())

EitherD-wp-is-weakest (EitherD-either f _ (Left  x)) P Prun = (λ where _ refl → EitherD-wp-is-weakest (f x) P Prun) , (λ _ ())
EitherD-wp-is-weakest (EitherD-either _ f (Right y)) P Prun = (λ _ ()) , (λ where _ refl → EitherD-wp-is-weakest (f y) P Prun)
EitherD-wp-is-weakest (EitherD-maybe m f nothing)    P Prun = (const (EitherD-wp-is-weakest m P Prun)) , (λ _ ())
EitherD-wp-is-weakest (EitherD-maybe m f (just j))   P Prun = (λ ()) , λ where _ refl → EitherD-wp-is-weakest (f j) P Prun

EitherD-⇒
  : ∀ {E A} {P Q : EitherD-Post E A}
  → ∀ m → EitherD-weakestPre m P
  → (EitherD-Post-⇒ P Q)
  → EitherD-weakestPre m Q
EitherD-⇒ {P = Post₁} {Post₂} (LeftD x )         pre pf = pf (Left x ) pre
EitherD-⇒ {P = Post₁} {Post₂} (RightD x)         pre pf = pf (Right x) pre
EitherD-⇒ {P = Post₁} {Post₂} (EitherD-bind m x) pre pf =
  EitherD-⇒ m pre P⇒Q
  where
    P⇒Q : EitherD-Post-⇒ (EitherD-weakestPre-bindPost x Post₁)
                         (EitherD-weakestPre-bindPost x Post₂)
    P⇒Q (Left  rL) Pr = pf (Left rL) Pr
    P⇒Q (Right rR) Pr .rR refl = EitherD-⇒ (x rR) (Pr rR refl) pf
EitherD-⇒ {Post₁} {Post₂} (EitherD-if (otherwise≔ x)) pre pf = EitherD-⇒ x pre pf
EitherD-⇒ {Post₁} {Post₂} (EitherD-if (clause (x ≔ x₂) x₁)) (pre₁ , pre₂) pf =
    (λ x≡true  → EitherD-⇒ x₂ (pre₁ x≡true) pf)
  , (λ x≡false → EitherD-⇒ (EitherD-if x₁) (pre₂ x≡false) pf)
proj₁ (EitherD-⇒ {Post₁} {Post₂} (EitherD-either x₁ x₂ (Left  x)) (pre₁ , pre₂) pf) .x refl =
       EitherD-⇒ (x₁ x) (pre₁ x refl) pf
proj₂ (EitherD-⇒ {Post₁} {Post₂} (EitherD-either x₁ x₂ (Right x)) (pre₁ , pre₂) pf) .x refl =
       EitherD-⇒ (x₂ x) (pre₂ x refl) pf
proj₁ (EitherD-⇒ {Post₁} {Post₂} (EitherD-maybe m x₁ .nothing) (pre₁ , pre₂) pf) refl   =
       EitherD-⇒ m      (pre₁   refl) pf
proj₂ (EitherD-⇒ {Post₁} {Post₂} (EitherD-maybe m x₁ (just x)) (pre₁ , pre₂) pf) j refl =
       EitherD-⇒ (x₁ j) (pre₂ j refl) pf

EitherD-⇒-bind :
    ∀ {E} {A} {P : EitherD-Post E A}
    → {Q : EitherD-Post E B}
    → {f : A → EitherD E B}
    → ∀ m → EitherD-weakestPre m P
    → EitherD-Post-⇒ P (EitherD-weakestPre-bindPost f Q)
    → EitherD-weakestPre (EitherD-bind m f) Q
EitherD-⇒-bind = EitherD-⇒

EitherD-vacuous : ∀ (m : EitherD E A) → EitherD-weakestPre m (const Unit)
EitherD-vacuous (LeftD x)                        = unit
EitherD-vacuous (RightD x)                       = unit
EitherD-vacuous (EitherD-if (otherwise≔ x))      = EitherD-vacuous x
EitherD-vacuous (EitherD-if (clause (b ≔ x) x₁)) = (const (EitherD-vacuous x)) , (const (EitherD-vacuous (EitherD-if x₁)))
EitherD-vacuous (EitherD-either x₁ x₂ x)         = (λ x₃ _ → EitherD-vacuous (x₁ x₃)) , (λ y _ → EitherD-vacuous (x₂ y))
EitherD-vacuous (EitherD-maybe m x₁ x)           = (const (EitherD-vacuous m)) , λ j _ → EitherD-vacuous (x₁ j)
EitherD-vacuous (EitherD-bind m x)               = EitherD-⇒-bind m (EitherD-vacuous m) λ { (Left  _) _ → unit
                                                                                          ; (Right _) _ → λ c _ → EitherD-vacuous (x c) }

