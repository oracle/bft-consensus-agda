open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.BasicTypes


module LibraBFT.Concrete.Util.HashMap where

  -- Update a function of type A → B on one input, given a decidability instance for A's
  -- The syntax is slightly ugly, but I couldn't do better in reasonable time
  -- TODO: Move somewhere more generic

  overrideOK : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
             → (f : A → B)
             → (a : A)
             → (b : B)
             → (a′ : A)
             → (f′ : A → B)
             → Set (ℓ₁ ℓ⊔ ℓ₂)
  overrideOK f a b a′ f′ = (a′ ≢ a × f′ a′ ≡ f a′) ⊎ (a′ ≡ a × f′ a′ ≡ b)

  overrideProp : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
               → (f : A → B)
               → (a : A)
               → (b : B)
               → (f′ : A → B)
               → Set (ℓ₁ ℓ⊔ ℓ₂)
  overrideProp f a b f′ = ∀ a′ → overrideOK f a b a′ f′

  overrideFn : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
             (f : A → B)
           → (a : A) → (b : B)
           → ((a₁ : A) → (a₂ : A) → (Dec (a₁ ≡ a₂)))
           → Σ ( A → B ) (λ f′ → overrideProp f a b f′)
  overrideFn {A = A} {B = B} f a b _≟xx_ =
     let f′ = (λ a₂ → selectVal f a b a₂)
     in f′ ,  (λ a₂ → selectPrf f a b a₂)

     where selectVal : (f : A → B) → (a : A) → (b : B) → (a₂ : A) → B
           selectVal f a b a₂ with a₂ ≟xx a
           ...| yes _ = b
           ...| no  _ = f a₂
           selectPrf : (f : A → B) → (a : A) → (b : B) → (a₂ : A) → overrideOK f a b a₂ (λ a₃ → selectVal f a b a₃)
           selectPrf f a b a₂ with a₂ ≟xx a
           ...| yes refl = inj₂ ( refl , refl )
           ...| no  a₂≢a = inj₁ ( a₂≢a , refl )

  _[_:=_,_] : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
             (f : A → B)
           → (a : A) → (b : B)
           → (_≟_ : (a₁ : A) → (a₂ : A) → (Dec (a₁ ≡ a₂)))
           → Σ ( A → B ) (λ f′ → overrideProp f a b f′)
  _[_:=_,_] {ℓ₁} {ℓ₂} {A = A} {B = B} f a₁ b _≟xx_ = overrideFn {ℓ₁} {ℓ₂} {A} {B} f a₁ b _≟xx_


  HashMap : ∀{ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ℓ⊔ ℓ₂)
  HashMap K V = K → Maybe V

  emptyHM : ∀ {K V : Set} → HashMap K V
  emptyHM {K} {V} k = nothing

  _∈HM_ : ∀ {ℓ₁ ℓ₂}{K : Set ℓ₁} {V : Set ℓ₂} (k : K) → HashMap K V → Set ℓ₂
  k ∈HM hm = ∃[ v ]( hm k ≡ just v )

  _∈HM?_ : ∀ {ℓ₁ ℓ₂}{K : Set ℓ₁} {V : Set ℓ₂} → (k : K) → (hm : HashMap K V) → Dec (k ∈HM hm)
  k ∈HM? hm with hm k
  ...| just x  = yes ((x , refl))
  ...| nothing = no (λ ())

  ∈HM-irrelevant : ∀{ℓ₁ ℓ₂}{K : Set ℓ₁}{V : Set ℓ₂}(k : K)
                 → (m : HashMap K V)(p₀ p₁ : k ∈HM m)
                 → p₀ ≡ p₁
  ∈HM-irrelevant k m (e , prf) (e' , prf') 
    with m k
  ...| just x 
    with prf | prf'
  ...| refl | refl = refl 

  emptyIsEmpty : ∀ {K : Set} {V : Set} {k : K} → ¬ (k ∈HM emptyHM {K} {V})
  emptyIsEmpty {k = k} = λ ()

