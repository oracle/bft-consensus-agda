{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Level using (0ℓ)
open import LibraBFT.Prelude

-- This module incldes various Agda lemmas that are independent of the project's domain

module LibraBFT.Lemmas where

 cong₃ : ∀{a b c d}{A : Set a}{B : Set b}{C : Set c}{D : Set d}
       → (f : A → B → C → D) → ∀{x y u v m n} → x ≡ y → u ≡ v → m ≡ n
       → f x u m ≡ f y v n
 cong₃ f refl refl refl = refl

 ≡-pi : ∀{a}{A : Set a}{x y : A}(p q : x ≡ y) → p ≡ q
 ≡-pi refl refl = refl

 Unit-pi : {u1 u2 : Unit}
         → u1 ≡ u2
 Unit-pi {unit} {unit} = refl

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

 filter-++-[]
   : ∀ {a p} {A : Set a} {P : (a : A) → Set p}
     → ∀ xs ys (p : (a : A) → Dec (P a))
     → List-filter p xs ≡ [] → List-filter p ys ≡ []
     → List-filter p (xs ++ ys) ≡ []
 filter-++-[] xs ys p pf₁ pf₂ rewrite List-filter-++ p xs ys | pf₁ | pf₂ = refl

 filter-∪?-[]₁
   : ∀ {a p} {A : Set a} {P Q : (a : A) → Set p}
     → ∀ xs (p : (a : A) → Dec (P a)) (q : (a : A) → Dec (Q a))
     → List-filter (p ∪? q) xs ≡ []
     → List-filter p xs ≡ []
 filter-∪?-[]₁ [] p q pf = refl
 filter-∪?-[]₁ (x ∷ xs) p q pf
   with p x
 ...| no  proof₁
   with q x
 ...| no  proof₂ = filter-∪?-[]₁ xs p q pf
 filter-∪?-[]₁ (x ∷ xs) p q () | no proof₁ | yes proof₂
 filter-∪?-[]₁ (x ∷ xs) p q () | yes proof

 filter-∪?-[]₂
   : ∀ {a p} {A : Set a} {P Q : (a : A) → Set p}
     → ∀ xs (p : (a : A) → Dec (P a)) (q : (a : A) → Dec (Q a))
     → List-filter (p ∪? q) xs ≡ []
     → List-filter q xs ≡ []
 filter-∪?-[]₂ [] p q pf = refl
 filter-∪?-[]₂ (x ∷ xs) p q pf
   with p x
 ...| no  proof₁
   with q x
 ...| no  proof₂ = filter-∪?-[]₂ xs p q pf
 filter-∪?-[]₂ (x ∷ xs) p q () | no proof₁ | yes proof₂
 filter-∪?-[]₂ (x ∷ xs) p q () | yes proof

 data All-vec {ℓ} {A : Set ℓ} (P : A → Set ℓ) : ∀ {n} → Vec {ℓ} A n → Set (Level.suc ℓ) where
   []  : All-vec P []
   _∷_ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All-vec P xs) → All-vec P (x ∷ xs)

 ≤-unstep : ∀{m n} → suc m ≤ n → m ≤ n
 ≤-unstep (s≤s ss) = ≤-step ss

 ≡⇒≤ : ∀{m n} → m ≡ n → m ≤ n
 ≡⇒≤ refl = ≤-refl

 ∈-cong : ∀{a b}{A : Set a}{B : Set b}{x : A}{l : List A}
        → (f : A → B) → x ∈ l → f x ∈ List-map f l
 ∈-cong f (here px) = here (cong f px)
 ∈-cong f (there hyp) = there (∈-cong f hyp)

 All-self : ∀{a}{A : Set a}{xs : List A} → All (_∈ xs) xs
 All-self = All-tabulate (λ x → x)

 All-reduce⁺
   : ∀{a b}{A : Set a}{B : Set b}{Q : A → Set}{P : B → Set}
   → { xs : List A }
   → (f : ∀{x} → Q x → B)
   → (∀{x} → (prf : Q x) → P (f prf))
   → (all : All Q xs)
   → All P (All-reduce f all)
 All-reduce⁺ f hyp []         = []
 All-reduce⁺ f hyp (ax ∷ axs) = (hyp ax) ∷ All-reduce⁺ f hyp axs

 All-reduce⁻
   : ∀{a b}{A : Set a}{B : Set b}
     {Q : A → Set}
   → { xs : List A }
   → ∀ {vdq}
   → (f : ∀{x} → Q x → B)
   → (all : All Q xs)
   → vdq ∈ All-reduce f all
   → ∃[ v ] ∃[ v∈xs ] (vdq ≡ f {v} v∈xs)
 All-reduce⁻ {Q = Q} {(h ∷ _)} {vdq} f (px ∷ pxs) (here refl)  = h , px , refl
 All-reduce⁻ {Q = Q} {(_ ∷ t)} {vdq} f (px ∷ pxs) (there vdq∈) = All-reduce⁻ {xs = t} f pxs vdq∈

 List-index : ∀ {A : Set} → (_≟A_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)) → A → (l : List A) → Maybe (Fin (length l))
 List-index _≟A_ x l with break (_≟A x) l
 ...| not≡ , _ with length not≡ <? length l
 ...| no  _     = nothing
 ...| yes found = just ( fromℕ< {length not≡} {length l} found)

 nats : ℕ → List ℕ
 nats 0 = []
 nats (suc n) = (nats n) ++ (n ∷ [])

 _ : nats 4 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
 _ = refl

 _ : Maybe-map toℕ (List-index _≟_ 2 (nats 4)) ≡ just 2
 _ = refl

 _ : Maybe-map toℕ (List-index _≟_ 4 (nats 4)) ≡ nothing
 _ = refl

 allDistinct : ∀ {A : Set} → List A → Set
 allDistinct l = ∀ (i j : Σ ℕ (_< length l)) →
                   proj₁ i ≡ proj₁ j
                   ⊎ List-lookup l (fromℕ< (proj₂ i)) ≢ List-lookup l (fromℕ< (proj₂ j))

 postulate -- TODO-1: currently unused; prove it, if needed
   allDistinct? : ∀ {A : Set} → {≟A : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)} → (l : List A) → Dec (allDistinct l)

  -- Extends an arbitrary relation to work on the head of
  -- the supplied list, if any.
 data OnHead {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []   : OnHead P x []
    on-∷ : ∀{y ys} → P x y → OnHead P x (y ∷ ys)

  -- Establishes that a list is sorted according to the supplied
  -- relation.
 data IsSorted {A : Set}(_<_ : A → A → Set) : List A → Set where
    []  : IsSorted _<_ []
    _∷_ : ∀{x xs} → OnHead _<_ x xs → IsSorted _<_ xs → IsSorted _<_ (x ∷ xs)

 OnHead-prop : ∀{A}(P : A → A → Set)(x : A)(l : List A)
             → Irrelevant P
             → isPropositional (OnHead P x l)
 OnHead-prop P x [] hyp [] [] = refl
 OnHead-prop P x (x₁ ∷ l) hyp (on-∷ x₂) (on-∷ x₃) = cong on-∷ (hyp x₂ x₃)

 IsSorted-prop : ∀{A}(_<_ : A → A → Set)(l : List A)
               → Irrelevant _<_
               → isPropositional (IsSorted _<_ l)
 IsSorted-prop _<_ [] hyp [] []                  = refl
 IsSorted-prop _<_ (x ∷ l) hyp (x₁ ∷ a) (x₂ ∷ b)
   = cong₂ _∷_ (OnHead-prop _<_ x l hyp x₁ x₂)
               (IsSorted-prop _<_ l hyp a b)

 IsSorted-map⁻ : {A : Set}{_≤_ : A → A → Set}
               → {B : Set}(f : B → A)(l : List B)
               → IsSorted (λ x y → f x ≤ f y) l
               → IsSorted _≤_ (List-map f l)
 IsSorted-map⁻ f .[] [] = []
 IsSorted-map⁻ f .(_ ∷ []) (x ∷ []) = [] ∷ []
 IsSorted-map⁻ f .(_ ∷ _ ∷ _) (on-∷ x ∷ (x₁ ∷ is)) = (on-∷ x) ∷ IsSorted-map⁻ f _ (x₁ ∷ is)

 transOnHead : ∀ {A} {l : List A} {y x : A} {_<_ : A → A → Set}
              → Transitive _<_
              → OnHead _<_ y l
              → x < y
              → OnHead _<_ x l
 transOnHead _ [] _ = []
 transOnHead trans (on-∷ y<f) x<y = on-∷ (trans x<y y<f)

 ++-OnHead : ∀ {A} {xs ys : List A} {y : A} {_<_ : A → A → Set}
           → OnHead _<_ y xs
           → OnHead _<_ y ys
           → OnHead _<_ y (xs ++ ys)
 ++-OnHead []         y<y₁ = y<y₁
 ++-OnHead (on-∷ y<x) _    = on-∷ y<x

 h∉t : ∀ {A} {t : List A} {h : A} {_<_ : A → A → Set}
     → Irreflexive _<_ _≡_ → Transitive _<_
     → IsSorted _<_ (h ∷ t)
     → h ∉ t
 h∉t irfl trans (on-∷ h< ∷ sxs) (here refl) = ⊥-elim (irfl h< refl)
 h∉t irfl trans (on-∷ h< ∷ (x₁< ∷ sxs)) (there h∈t)
   = h∉t irfl trans ((transOnHead trans x₁< h<) ∷ sxs) h∈t

 ≤-head : ∀ {A} {l : List A} {x y : A} {_<_ : A → A → Set} {_≤_ : A → A → Set}
        → Reflexive _≤_ → Trans _<_ _≤_ _≤_
        → y ∈ (x ∷ l) → IsSorted _<_ (x ∷ l)
        → _≤_ x y
 ≤-head ref≤ trans (here refl) _ = ref≤
 ≤-head ref≤ trans (there y∈) (on-∷ x<x₁ ∷ sl) = trans x<x₁ (≤-head ref≤ trans y∈ sl)

 -- TODO-1 : Better name and/or replace with library property
 Any-sym : ∀ {a b}{A : Set a}{B : Set b}{tgt : B}{l : List A}{f : A → B}
         → Any (λ x → tgt ≡ f x) l
         → Any (λ x → f x ≡ tgt) l
 Any-sym (here x)  = here (sym x)
 Any-sym (there x) = there (Any-sym x)

 Any-lookup-correct :  ∀ {a b}{A : Set a}{B : Set b}{tgt : B}{l : List A}{f : A → B}
                    → (p : Any (λ x → f x ≡ tgt) l)
                    → Any-lookup p ∈ l
 Any-lookup-correct (here px) = here refl
 Any-lookup-correct (there p) = there (Any-lookup-correct p)

 Any-lookup-correctP :  ∀ {a}{A : Set a}{l : List A}{P : A → Set}
                     → (p : Any P l)
                     → Any-lookup p ∈ l
 Any-lookup-correctP (here px) = here refl
 Any-lookup-correctP (there p) = there (Any-lookup-correctP p)

 Any-witness : ∀ {a b} {A : Set a} {l : List A} {P : A → Set b}
             → (p : Any P l) → P (Any-lookup p)
 Any-witness (here px) = px
 Any-witness (there x) = Any-witness x

 -- TODO-1: there is probably a library property for this.
 ∈⇒Any : ∀ {A : Set}{x : A}
       → {xs : List A}
       → x ∈ xs
       → Any (_≡ x) xs
 ∈⇒Any {x = x} (here refl) = here refl
 ∈⇒Any {x = x} {h ∷ t} (there xxxx) = there (∈⇒Any {xs = t} xxxx)

 false≢true : false ≢ true
 false≢true ()

 witness : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → x ∈ xs → All P xs → P x
 witness x y = All-lookup y x

 maybe-⊥ : ∀{a}{A : Set a}{x : A}{y : Maybe A}
         → y ≡ just x
         → y ≡ nothing
         → ⊥
 maybe-⊥ () refl

 Maybe-map-cool : ∀ {S S₁ : Set} {f : S → S₁} {x : Maybe S} {z}
                → Maybe-map f x ≡ just z
                → x ≢ nothing
 Maybe-map-cool {x = nothing} ()
 Maybe-map-cool {x = just y} prf = λ x → ⊥-elim (maybe-⊥ (sym x) refl)

 Maybe-map-cool-1 : ∀ {S S₁ : Set} {f : S → S₁} {x : Maybe S} {z}
                  → Maybe-map f x ≡ just z
                  → Σ S (λ x' → f x' ≡ z)
 Maybe-map-cool-1 {x = nothing} ()
 Maybe-map-cool-1 {x = just y} {z = z} refl = y , refl

 Maybe-map-cool-2 : ∀ {S S₁ : Set} {f : S → S₁} {x : S} {z}
                  → f x ≡ z
                  → Maybe-map f (just x) ≡ just z
 Maybe-map-cool-2 {S}{S₁}{f}{x}{z} prf rewrite prf = refl

 T⇒true : ∀ {a : Bool} → T a → a ≡ true
 T⇒true {true} _ = refl

 isJust : ∀ {A : Set}{aMB : Maybe A}{a : A}
        → aMB ≡ just a
        → Is-just aMB
 isJust refl = just tt

 to-witness-isJust-≡ : ∀ {A : Set}{aMB : Maybe A}{a prf}
                     → to-witness (isJust {aMB = aMB} {a} prf) ≡ a
 to-witness-isJust-≡ {aMB = just a'} {a} {prf}
    with to-witness-lemma (isJust {aMB = just a'} {a} prf) refl
 ...| xxx = just-injective (trans (sym xxx) prf)

 deMorgan : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
 deMorgan (inj₁ ¬a) = λ a×b → ¬a (proj₁ a×b)
 deMorgan (inj₂ ¬b) = λ a×b → ¬b (proj₂ a×b)

 ¬subst : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
        → {x y : A}
        → ¬ (P x)
        → y ≡ x
        → ¬ (P y)
 ¬subst px refl = px

 ∸-suc-≤ : ∀ (x w : ℕ) → suc x ∸ w ≤ suc (x ∸ w)
 ∸-suc-≤ x zero = ≤-refl
 ∸-suc-≤ zero (suc w) rewrite 0∸n≡0 w = z≤n
 ∸-suc-≤ (suc x) (suc w) = ∸-suc-≤ x w

 m∸n≤o⇒m∸o≤n : ∀ (x z w : ℕ) → x ∸ z ≤ w → x ∸ w ≤ z
 m∸n≤o⇒m∸o≤n x zero w p≤ rewrite m≤n⇒m∸n≡0 p≤ = z≤n
 m∸n≤o⇒m∸o≤n zero (suc z) w p≤ rewrite 0∸n≡0 w = z≤n
 m∸n≤o⇒m∸o≤n (suc x) (suc z) w p≤ = ≤-trans (∸-suc-≤ x w) (s≤s (m∸n≤o⇒m∸o≤n x z w p≤))

 tail-⊆ : ∀ {A : Set} {x} {xs ys : List A}
        → (x ∷ xs) ⊆List ys
        → xs ⊆List ys
 tail-⊆ xxs⊆ys x∈xs = xxs⊆ys (there x∈xs)

 allDistinctTail : ∀ {A : Set} {x} {xs : List A}
                 → allDistinct (x ∷ xs)
                 → allDistinct xs
 allDistinctTail allDist (i , i<l) (j , j<l)
   with allDist (suc i , s≤s i<l) (suc j , s≤s j<l)
 ...| inj₁ 1+i≡1+j = inj₁ (cong pred 1+i≡1+j)
 ...| inj₂ lookup≢ = inj₂ lookup≢

 ∈-Any-Index-elim : ∀ {A : Set} {x y} {ys : List A} (x∈ys : x ∈ ys)
                  → x ≢ y → y ∈ ys
                  → y ∈ ys ─ Any-index x∈ys
 ∈-Any-Index-elim (here refl)  x≢y (here refl)  = ⊥-elim (x≢y refl)
 ∈-Any-Index-elim (here refl)  _   (there y∈ys) = y∈ys
 ∈-Any-Index-elim (there _)    _   (here refl)  = here refl
 ∈-Any-Index-elim (there x∈ys) x≢y (there y∈ys) = there (∈-Any-Index-elim x∈ys x≢y y∈ys)

 ∉∧⊆List⇒∉ : ∀ {A : Set} {x} {xs ys : List A}
           → x ∉ xs → ys ⊆List xs
           → x ∉ ys
 ∉∧⊆List⇒∉ x∉xs ys∈xs x∈ys = ⊥-elim (x∉xs (ys∈xs x∈ys))

 allDistinctʳʳ : ∀ {A : Set} {x x₁ : A} {xs : List A}
               → allDistinct (x ∷ x₁ ∷ xs)
               → allDistinct (x ∷ xs)
 allDistinctʳʳ _ (zero , _) (zero , _) = inj₁ refl
 allDistinctʳʳ allDist (zero , i<l) (suc j , j<l)
   with allDist (0 , s≤s z≤n) (suc (suc j) , s≤s j<l)
 ...| inj₂ x≢lookup
      = inj₂ λ x≡lkpxs → ⊥-elim (x≢lookup x≡lkpxs)
 allDistinctʳʳ allDist (suc i , i<l) (zero , j<l)
   with allDist (suc (suc i) , s≤s i<l) (0 , s≤s z≤n)
 ...| inj₂ x≢lookup
      = inj₂ λ x≡lkpxs → ⊥-elim (x≢lookup x≡lkpxs)
 allDistinctʳʳ allDist (suc i , i<l) (suc j , j<l)
   with allDist (2 + i , (s≤s i<l)) (2 + j , s≤s j<l)
 ...| inj₁ si≡sj   = inj₁ (cong pred si≡sj)
 ...| inj₂ lookup≡ = inj₂ lookup≡

 allDistinct⇒∉ : ∀ {A : Set} {x} {xs : List A}
               → allDistinct (x ∷ xs)
               → x ∉ xs
 allDistinct⇒∉ allDist (here x≡x₁)
   with allDist (0 , s≤s z≤n) (1 , s≤s (s≤s z≤n))
 ... | inj₂ x≢x₁ = ⊥-elim (x≢x₁ x≡x₁)
 allDistinct⇒∉ allDist (there x∈xs)
   = allDistinct⇒∉ (allDistinctʳʳ allDist) x∈xs

 sumListMap : ∀ {A : Set} {x} {xs : List A} (f : A → ℕ) → (x∈xs : x ∈ xs)
            → f-sum f xs ≡ f x + f-sum f (xs ─ Any-index x∈xs)
 sumListMap _ (here refl)  = refl
 sumListMap {_} {x} {x₁ ∷ xs} f (there x∈xs)
   rewrite sumListMap f x∈xs
         | sym (+-assoc (f x) (f x₁) (f-sum f (xs ─ Any-index x∈xs)))
         | +-comm (f x) (f x₁)
         | +-assoc (f x₁) (f x) (f-sum f (xs ─ Any-index x∈xs)) = refl

 lookup⇒Any : ∀ {A : Set} {xs : List A} {P : A → Set} (i : Fin (length xs))
            → P (List-lookup xs i) → Any P xs
 lookup⇒Any {_} {_ ∷ _} zero    px = here px
 lookup⇒Any {_} {_ ∷ _} (suc i) px = there (lookup⇒Any i px)

 x∉→AllDistinct : ∀ {A : Set} {x} {xs : List A}
                → allDistinct xs
                → x ∉ xs
                → allDistinct (x ∷ xs)
 x∉→AllDistinct _ _ (0 , _) (0 , _) = inj₁ refl
 x∉→AllDistinct _ x∉xs (0 , _) (suc j , j<l)
   = inj₂ (λ x≡lkp → x∉xs (lookup⇒Any (fromℕ< (≤-pred j<l)) x≡lkp))
 x∉→AllDistinct _ x∉xs (suc i , i<l) (0 , _)
   = inj₂ (λ x≡lkp → x∉xs (lookup⇒Any (fromℕ< (≤-pred i<l)) (sym x≡lkp)))
 x∉→AllDistinct allDist x∉xs (suc i , i<l) (suc j , j<l)
   with allDist (i , (≤-pred i<l)) (j , (≤-pred j<l))
 ...| inj₁ i≡j   = inj₁ (cong suc i≡j)
 ...| inj₂ lkup≢ = inj₂ lkup≢

 sum-f∘g : ∀ {A B : Set} (xs : List A) (g : B → ℕ) (f : A → B)
           → f-sum (g ∘ f) xs ≡ f-sum g (List-map f xs)
 sum-f∘g xs g f = cong sum (List-map-compose xs)

 module DecLemmas {A : Set} (_≟D_ : Decidable {A = A} (_≡_)) where

   _∈?_ : ∀ (x : A) → (xs : List A) → Dec (Any (x ≡_) xs)
   x ∈? xs = Any-any (x ≟D_) xs

   y∉xs⇒Allxs≢y : ∀ {xs : List A} {x y}
                → y ∉ (x ∷ xs)
                → x ≢ y × y ∉ xs
   y∉xs⇒Allxs≢y {xs} {x} {y} y∉
     with y ∈? xs
   ...| yes y∈xs = ⊥-elim (y∉ (there y∈xs))
   ...| no  y∉xs
     with x ≟D y
   ...| yes x≡y = ⊥-elim (y∉ (here (sym x≡y)))
   ...| no  x≢y = x≢y , y∉xs

   ⊆List-Elim :  ∀ {x} {xs ys : List A} (x∈ys : x ∈ ys)
              → x ∉ xs → xs ⊆List ys
              → xs ⊆List ys ─ Any-index x∈ys
   ⊆List-Elim (here refl) x∉xs xs∈ys x₂∈xs
     with xs∈ys x₂∈xs
   ...| here refl  = ⊥-elim (x∉xs x₂∈xs)
   ...| there x∈xs = x∈xs
   ⊆List-Elim (there x∈ys) x∉xs xs∈ys x₂∈xxs
     with x₂∈xxs
   ...| there x₂∈xs
         = ⊆List-Elim (there x∈ys) (proj₂ (y∉xs⇒Allxs≢y x∉xs)) (tail-⊆ xs∈ys) x₂∈xs
   ...| here refl
     with xs∈ys x₂∈xxs
   ...| here refl = here refl
   ...| there x₂∈ys
         = there (∈-Any-Index-elim x∈ys (≢-sym (proj₁ (y∉xs⇒Allxs≢y x∉xs))) x₂∈ys)

   sum-⊆-≤ : ∀ {ys} (xs : List A) (f : A → ℕ)
           → allDistinct xs
           → xs ⊆List ys
           → f-sum f xs ≤ f-sum f ys
   sum-⊆-≤ [] _ _ _ = z≤n
   sum-⊆-≤ (x ∷ xs) f dxs xs⊆ys
      rewrite sumListMap f (xs⊆ys (here refl))
      = let x∉xs    = allDistinct⇒∉ dxs
            xs⊆ysT  = tail-⊆ xs⊆ys
            xs⊆ys-x = ⊆List-Elim (xs⊆ys (here refl)) x∉xs xs⊆ysT
            disTail = allDistinctTail dxs
       in +-monoʳ-≤ (f x) (sum-⊆-≤ xs f disTail xs⊆ys-x)

   intersect : List A → List A → List A
   intersect xs [] = []
   intersect xs (y ∷ ys)
     with y ∈? xs
   ...| yes _ = y ∷ intersect xs ys
   ...| no  _ = intersect xs ys

   union : List A → List A → List A
   union xs [] = xs
   union xs (y ∷ ys)
     with y ∈? xs
   ...| yes _ = union xs ys
   ...| no  _ = y ∷ union xs ys

   ∈-intersect : ∀ (xs ys : List A) {α}
               → α ∈ intersect xs ys
               → α ∈ xs × α ∈ ys
   ∈-intersect xs (y ∷ ys) α∈int
     with y ∈? xs  | α∈int
   ...| no  y∉xs   | α∈        = ×-map₂ there (∈-intersect xs ys α∈)
   ...| yes y∈xs   | here refl = y∈xs , here refl
   ...| yes y∈xs   | there α∈  = ×-map₂ there (∈-intersect xs ys α∈)

   x∉⇒x∉intersect : ∀ {x} {xs ys : List A}
                    → x ∉ xs ⊎ x ∉ ys
                    → x ∉ intersect xs ys
   x∉⇒x∉intersect {x} {xs} {ys} x∉ x∈int
     = contraposition (∈-intersect xs ys) (deMorgan x∉) x∈int

   intersectDistinct : ∀ (xs ys : List A)
                     → allDistinct xs → allDistinct ys
                     → allDistinct (intersect xs ys)
   intersectDistinct xs (y ∷ ys) dxs dys
     with y ∈? xs
   ...| yes y∈xs = let distTail  = allDistinctTail dys
                       intDTail  = intersectDistinct xs ys dxs distTail
                       y∉intTail = x∉⇒x∉intersect (inj₂ (allDistinct⇒∉ dys))
                   in x∉→AllDistinct intDTail y∉intTail
   ...| no  y∉xs = intersectDistinct xs ys dxs (allDistinctTail dys)

   x∉⇒x∉union : ∀ {x} {xs ys : List A}
              → x ∉ xs × x ∉ ys
              → x ∉ union xs ys
   x∉⇒x∉union {_} {_} {[]} (x∉xs , _) x∈∪ = ⊥-elim (x∉xs x∈∪)
   x∉⇒x∉union {x} {xs} {y ∷ ys} (x∉xs , x∉ys) x∈union
     with y ∈? xs  | x∈union
   ...| yes y∈xs   | x∈∪
        = ⊥-elim (x∉⇒x∉union (x∉xs , (proj₂ (y∉xs⇒Allxs≢y x∉ys))) x∈∪)
   ...| no y∉xs    | here refl
        = ⊥-elim (proj₁ (y∉xs⇒Allxs≢y x∉ys) refl)
   ...| no y∉xs    | there x∈∪
        = ⊥-elim (x∉⇒x∉union (x∉xs , (proj₂ (y∉xs⇒Allxs≢y x∉ys))) x∈∪)

   unionDistinct : ∀ (xs ys : List A)
               → allDistinct xs → allDistinct ys
               → allDistinct (union xs ys)
   unionDistinct xs [] dxs dys = dxs
   unionDistinct xs (y ∷ ys) dxs dys
      with y ∈? xs
   ...| yes y∈xs = unionDistinct xs ys dxs (allDistinctTail dys)
   ...| no  y∉xs = let distTail  = allDistinctTail dys
                       uniDTail  = unionDistinct xs ys dxs distTail
                       y∉intTail = x∉⇒x∉union (y∉xs , allDistinct⇒∉ dys)
                   in x∉→AllDistinct uniDTail y∉intTail

   sumIntersect≤ : ∀ (xs ys : List A) (f : A → ℕ)
                 → f-sum f (intersect xs ys) ≤ f-sum f (xs ++ ys)
   sumIntersect≤ _ [] _ = z≤n
   sumIntersect≤ xs (y ∷ ys) f
     with y ∈? xs
   ...| yes y∈xs rewrite map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | sym (+-assoc (f-sum f xs) (f y) (f-sum f ys))
                       | +-comm (f-sum f xs) (f y)
                       | +-assoc (f y) (f-sum f xs) (f-sum f ys)
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = +-monoʳ-≤ (f y) (sumIntersect≤ xs ys f)
   ...| no  y∉xs rewrite map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | +-comm (f y) (f-sum f ys)
                       | sym (+-assoc (f-sum f xs) (f-sum f ys) (f y))
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = ≤-stepsʳ (f y) (sumIntersect≤ xs ys f)

   list-index : ∀ (xs : List A) → A → Maybe (Fin (length xs))
   list-index [] x = nothing
   list-index (x ∷ xs) y
     with x ≟D y
   ...| yes x≡y = just zero
   ...| no  x≢y
      with list-index xs y
   ...| nothing = nothing
   ...| just i  = just (suc i)

