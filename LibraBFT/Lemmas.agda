open import LibraBFT.Prelude

open import Level using (0ℓ)

module LibraBFT.Lemmas where

 ≡-pi : ∀{a}{A : Set a}{x y : A}(p q : x ≡ y) → p ≡ q
 ≡-pi refl refl = refl

 ++-inj : ∀{a}{A : Set a}{m n o p : List A}
        → length m ≡ length n → m ++ o ≡ n ++ p
        → m ≡ n × o ≡ p
 ++-inj {m = []}     {x ∷ n} () hip
 ++-inj {m = x ∷ m}  {[]}    () hip
 ++-inj {m = []}     {[]}     lhip hip
   = refl , hip
 ++-inj {m = m ∷ ms} {n ∷ ns} lhip hip
   with ++-inj {m = ms} {ns} (suc-injective lhip) (proj₂ (∷-injective hip))
 ...| (mn , op) rewrite proj₁ (∷-injective hip)
    = cong (n ∷_) mn , op

 ++-abs : ∀{a}{A : Set a}{n : List A}(m : List A)
        → 1 ≤ length m → [] ≡ m ++ n → ⊥
 ++-abs [] ()
 ++-abs (x ∷ m) imp ()


 data All-vec {ℓ} {A : Set ℓ} (P : A → Set ℓ) : ∀ {n} → Vec {ℓ} A n → Set (Level.suc ℓ) where
   []  : All-vec P []
   _∷_ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All-vec P xs) → All-vec P (x ∷ xs)

 ≤-unstep : ∀{m n} → suc m ≤ n → m ≤ n
 ≤-unstep (s≤s ss) = ≤-step ss

 ≡⇒≤ : ∀{m n} → m ≡ n → m ≤ n
 ≡⇒≤ refl = ≤-refl

 _∈_ : ∀ {a} {A : Set a} → A → List A → Set a
 x ∈ l = Any (_≡ x) l

 {-Any-lookup-correct : ∀ {a} {A : Set a} {x : A} {l : List A} → (p : x ∈ l) → Any-lookup p ∈ l
 Any-lookup-correct (here refl) = here refl
 Any-lookup-correct (there p)   = there (Any-lookup-correct p )
-}
   -- Extends an arbitrary relation to work on the head of
  -- the supplied list, if any.
 data OnHead {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []  : OnHead P x []
    _∷_ : ∀{y ys} → P x y → OnHead P x (y ∷ ys)

  -- Estabilishes that a list is sorted according to the supplied
  -- relation.
 data IsSorted {A : Set}(_<_ : A → A → Set) : List A → Set where
    []  : IsSorted _<_ []
    _∷_ : ∀{x xs} → OnHead _<_ x xs → IsSorted _<_ xs → IsSorted _<_ (x ∷ xs)

 Any-lookup-correct :  ∀ {a b} {A : Set a} {B : Set b} {tgt : B} {l : List A} {f : A → B} → (p : Any (λ x → f x ≡ tgt) l) → Any-lookup p ∈ l
 Any-lookup-correct (here px) = here refl
 Any-lookup-correct (there p) = there (Any-lookup-correct p)

 witness : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → x ∈ xs → All P xs → P x
 witness {x = x} {xs = []} ()
 witness {P = P } {x = x} {xh ∷ xt} (here px) all = subst P px (All-head all)
 witness {x = x} {xh ∷ xt} (there x∈xt) all = witness x∈xt (All-tail all)
