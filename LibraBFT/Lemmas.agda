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

 List-index : ∀ {A : Set} → (_≟A_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)) → A → (l : List A) → Maybe (Fin (length l))
 List-index _≟A_ x l with break (_≟A x) l
 ...| not≡ , _ with length not≡ <? length l
 ...| no  _     = nothing
 ...| yes found = just ( fromℕ≤ {length not≡} {length l} found)

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
                   ⊎ List-lookup l (fromℕ≤ (proj₂ i)) ≢ List-lookup l (fromℕ≤ (proj₂ j))

 postulate -- TODO
   allDistinct? : ∀ {A : Set} → {≟A : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)} → (l : List A) → Dec (allDistinct l)

 {-Any-lookup-correct : ∀ {a} {A : Set a} {x : A} {l : List A} → (p : x ∈ l) → Any-lookup p ∈ l
 Any-lookup-correct (here refl) = here refl
 Any-lookup-correct (there p)   = there (Any-lookup-correct p )
-}
   -- Extends an arbitrary relation to work on the head of
  -- the supplied list, if any.
 data OnHead {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []   : OnHead P x []
    on-∷ : ∀{y ys} → P x y → OnHead P x (y ∷ ys)

  -- Estabilishes that a list is sorted according to the supplied
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

 Any-lookup-correct :  ∀ {a b}{A : Set a}{B : Set b}{tgt : B}{l : List A}{f : A → B} 
                    → (p : Any (λ x → f x ≡ tgt) l) 
                    → Any-lookup p ∈ l
 Any-lookup-correct (here px) = here refl
 Any-lookup-correct (there p) = there (Any-lookup-correct p)

 Any-witness : ∀ {a b} {A : Set a} {l : List A} {P : A → Set b}
             → (p : Any P l) → P (Any-lookup p)
 Any-witness (here px) = px
 Any-witness (there x) = Any-witness x
  

 witness : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → x ∈ xs → All P xs → P x
 witness x y = All-lookup y x

 maybe-⊥ : ∀{a}{A : Set a}{x : A}{y : Maybe A}
         → y ≡ just x
         → y ≡ nothing
         → ⊥
 maybe-⊥ () refl
