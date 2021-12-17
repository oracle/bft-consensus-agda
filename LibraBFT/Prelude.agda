{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This is a selection of useful functions and definitions
-- from the standard library that we tend to use a lot.

module LibraBFT.Prelude where

  open import Haskell.Prelude public

  open import Level
    renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
    public

  1ℓ : Level
  1ℓ = ℓ+1 0ℓ

  open import Agda.Builtin.Unit
    public

  open import Function
    using (_∘_; _∘′_; case_of_; _on_; _∋_)
    public
  identity = Function.id

  open import Data.Unit.NonEta
    public

  open import Data.Empty
    public

  -- NOTE: This function is defined to give extra documentation when discharging
  -- absurd cases where Agda can tell by pattern matching that `A` is not
  -- inhabited. For example:
  -- > absurd (just v ≡ nothing) case impossibleProof of λ ()
  infix 0 absurd_case_of_
  absurd_case_of_ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) {B : Set ℓ₂} → A → (A → ⊥) → B
  absurd A case x of f = ⊥-elim (f x)

  open import Data.Nat
    renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_; _≥?_ to _≥?ℕ_; compare to compareℕ; Ordering to Orderingℕ)
    public

  max = _⊔_
  min = _⊓_

  open import Data.Nat.Properties
    hiding (≡-irrelevant ; _≟_)
    public

  open import Data.List
    renaming (map to List-map ; filter to List-filter ; lookup to List-lookup;
              tabulate to List-tabulate; foldl to List-foldl)
    hiding (fromMaybe; [_])
    public

  open import Data.List.Properties
    renaming (≡-dec to List-≡-dec; length-map to List-length-map; map-compose to List-map-compose; filter-++ to List-filter-++; length-filter to List-length-filter)
    using (∷-injective; length-++; map-++-commute; sum-++-commute; map-tabulate; tabulate-lookup; ++-identityʳ; ++-identityˡ)
    public

  open import Data.List.Relation.Binary.Subset.Propositional
    renaming (_⊆_ to _⊆List_)
    public

  open import Data.List.Relation.Unary.Any
    using (Any; here; there)
    renaming (lookup to Any-lookup; map to Any-map; satisfied to Any-satisfied
             ;index to Any-index; any to Any-any)
    public

  open import Data.List.Relation.Unary.Any.Properties
    using    (¬Any[])
    renaming ( map⁺       to Any-map⁺
             ; map⁻       to Any-map⁻
             ; concat⁺    to Any-concat⁺
             ; concat⁻    to Any-concat⁻
             ; ++⁻        to Any-++⁻
             ; ++⁺ʳ       to Any-++ʳ
             ; ++⁺ˡ       to Any-++ˡ
             ; singleton⁻ to Any-singleton⁻
             ; tabulate⁺  to Any-tabulate⁺
             ; filter⁻    to Any-filter⁻
             )
    public

  open import Data.List.Relation.Unary.All
    using (All; []; _∷_)
    renaming (head     to All-head;   tail     to All-tail;
              lookup   to All-lookup; tabulate to All-tabulate;
              reduce   to All-reduce; map      to All-map)
    public

  open import Data.List.Relation.Unary.All.Properties
    hiding   (All-map)
    renaming ( tabulate⁻ to All-tabulate⁻
             ; tabulate⁺ to All-tabulate⁺
             ; map⁺      to All-map⁺
             ; map⁻      to All-map⁻
             ; ++⁺       to All-++
             )
    public

  open import Data.List.Membership.Propositional
    using (_∈_; _∉_)
    public

  open import Data.List.Membership.Propositional.Properties
    renaming (∈-filter⁺ to List-∈-filter⁺; ∈-filter⁻ to List-∈-filter⁻)
    public

  open import Data.Vec
    using (Vec; []; _∷_)
    renaming (replicate to Vec-replicate; lookup to Vec-lookup
             ;map to Vec-map; head to Vec-head; tail to Vec-tail
             ;updateAt to Vec-updateAt; tabulate to Vec-tabulate
             ;allFin to Vec-allFin; toList to Vec-toList; fromList to Vec-fromList
             ;_++_ to _Vec-++_)
    public

  open import Data.Vec.Relation.Unary.All
    using ([]; _∷_)
    renaming (All to Vec-All; lookup to Vec-All-lookup)
    public

  open import Data.Vec.Properties
    using ()
    renaming (updateAt-minimal to Vec-updateAt-minimal
             ;[]=⇒lookup to Vec-[]=⇒lookup
             ;lookup⇒[]= to Vec-lookup⇒[]=
             ;lookup∘tabulate to Vec-lookup∘tabulate
             ;≡-dec to Vec-≡-dec)
    public

  open import Data.List.Relation.Binary.Pointwise
    using (decidable-≡)
    public

  open import Data.Bool
    renaming (_≟_ to _≟Bool_)
    hiding (_≤?_; _<_; _<?_; _≤_; not)
    public

  open import Data.Maybe
    renaming (map to Maybe-map; zip to Maybe-zip ; _>>=_ to _Maybe->>=_)
    hiding (align; alignWith; zipWith)
    public

  -- a non-dependent eliminator
  maybeS : ∀ {a b} {A : Set a} {B : Set b} →
           (x : Maybe A) → B → ((x : A) → B) → B
  maybeS {B = B} x f t = maybe {B = const B} t f x

  open import Data.Maybe.Relation.Unary.Any
    renaming (Any to Maybe-Any; dec to Maybe-Any-dec)
    hiding (map; zip; zipWith; unzip ; unzipWith)
    public

  maybe-any-⊥ : ∀{a}{A : Set a} → Maybe-Any {A = A} (λ _ → ⊤) nothing → ⊥
  maybe-any-⊥ ()

  headMay : ∀ {A : Set} → List A → Maybe A
  headMay     []  = nothing
  headMay (x ∷ _) = just x

  lastMay : ∀ {A : Set} → List A → Maybe A
  lastMay          []  = nothing
  lastMay     (x ∷ []) = just x
  lastMay (_ ∷ x ∷ xs) = lastMay (x ∷ xs)

  open import Data.Maybe.Properties
    using (just-injective)
    renaming (≡-dec to Maybe-≡-dec)
    public

  open import Data.Fin
    using (Fin; suc; zero; fromℕ; fromℕ< ; toℕ ; cast)
    renaming (_≟_ to _≟Fin_; _≤?_ to _≤?Fin_; _≤_ to _≤Fin_ ; _<_ to _<Fin_;
              inject₁ to Fin-inject₁; inject+ to Fin-inject+; inject≤ to Fin-inject≤)
    public

  fins : (n : ℕ) → List (Fin n)
  fins n = Vec-toList (Vec-allFin n)

  open import Data.Fin.Properties
    using (toℕ-injective; toℕ<n)
    renaming (<-cmp to Fin-<-cmp; <⇒≢ to <⇒≢Fin; suc-injective to Fin-suc-injective)
    public

  open import Relation.Binary.PropositionalEquality
    hiding (decSetoid)
    public

  open import Relation.Binary.HeterogeneousEquality
    using (_≅_)
    renaming (cong to ≅-cong; cong₂ to ≅-cong₂)
    public

  open import Relation.Binary
    public

  ≡-irrelevant : ∀{a}{A : Set a} → Irrelevant {a} {A} _≡_
  ≡-irrelevant refl refl = refl

  to-witness-lemma : ∀{ℓ}{A : Set ℓ}{a : A}{f : Maybe A}(x : Is-just f)
                   → to-witness x ≡ a → f ≡ just a
  to-witness-lemma (just x) refl = refl

  open import Relation.Nullary
    hiding (Irrelevant; proof)
    public

  open import Relation.Nullary.Decidable
    hiding (map)
    public

  open import Data.Sum
    renaming (map to ⊎-map; map₁ to ⊎-map₁; map₂ to ⊎-map₂)
    public

  open import Data.Sum.Properties
    using (inj₁-injective ; inj₂-injective)
    public

  ⊎-elimˡ : ∀ {ℓ₀ ℓ₁}{A₀ : Set ℓ₀}{A₁ : Set ℓ₁} → ¬ A₀ → A₀ ⊎ A₁ → A₁
  ⊎-elimˡ ¬a = either (⊥-elim ∘ ¬a) id

  ⊎-elimʳ : ∀ {ℓ₀ ℓ₁}{A₀ : Set ℓ₀}{A₁ : Set ℓ₁} → ¬ A₁ → A₀ ⊎ A₁ → A₀
  ⊎-elimʳ ¬a = either id (⊥-elim ∘ ¬a)

  open import Data.Product
    renaming (map to ×-map; map₂ to ×-map₂; map₁ to ×-map₁; <_,_> to split; swap to ×-swap)
    hiding (zip)
    public

  open import Data.Product.Properties
    public

  module _ {ℓA} {A : Set ℓA} where
    NoneOfKind : ∀ {ℓ} {P : A → Set ℓ} → List A → (p : (a : A) → Dec (P a)) → Set ℓA
    NoneOfKind xs p = List-filter p xs ≡ []

    postulate -- TODO-1: Replace with or prove using library properties?  Move to Lemmas?
      NoneOfKind⇒ : ∀ {ℓ} {P : A → Set ℓ} {Q : A → Set ℓ} {xs : List A}
                  → (p : (a : A) → Dec (P a))
                  → {q : (a : A) → Dec (Q a)}
                  → (∀ {a} → P a → Q a)  -- TODO-1: Use proper notation (Relation.Unary?)
                  → NoneOfKind xs q
                  → NoneOfKind xs p

  infix 4 _<?ℕ_
  _<?ℕ_ : Decidable _<_
  m <?ℕ n = suc m ≤?ℕ n

  infix 0 if-yes_then_else_
  infix 0 if-dec_then_else_
  if-yes_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Dec A → (A → B) → (¬ A → B) → B
  if-yes (yes prf) then f else _ = f prf
  if-yes (no  prf) then _ else g = g prf

  if-dec_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Dec A → B → B → B
  if-dec x then f else g = if-yes x then const f else const g

  open import Relation.Nullary.Negation
    using (contradiction; contraposition)
    public

  open import Relation.Binary
    using (Setoid; IsPreorder)
    public

  open import Relation.Unary
    using (_∪_)
    public

  open import Relation.Unary.Properties
    using (_∪?_)
    public

  -- Injectivity for a function of two potentially different types (A and B) via functions to a
  -- common type (C).

  Injective' : ∀ {b c d e}{B : Set b}{C : Set c}{D : Set d} → (hB : B → D) → (hC : C → D) → (_≈_ : B → C → Set e) → Set _
  Injective' {C = C} hB hC _≈_ = ∀ {b c} → hB b ≡ hC c → b ≈ c

  Injective  : ∀ {c d e}{C : Set c}{D : Set d} → (h : C → D) → (_≈_ : Rel C e) → Set _
  Injective h _≈_ = Injective' h h _≈_

  Injective-≡ : ∀ {c d}{C : Set c}{D : Set d} → (h : C → D) → Set _
  Injective-≡ h = Injective h _≡_

  Injective-int : ∀{a b c d e}{A : Set a}{B : Set b}{C : Set c}{D : Set d}
                → (_≈_ : A → B → Set e)
                → (h  : C → D)
                → (f₁ : A → C)
                → (f₂ : B → C)
                → Set (a ℓ⊔ b ℓ⊔ d ℓ⊔ e)
  Injective-int _≈_ h f₁ f₂ = ∀ {a₁} {b₁} → h (f₁ a₁) ≡ h (f₂ b₁) → a₁ ≈ b₁

  NonInjective : ∀{a b c}{A : Set a}{B : Set b}
               → (_≈_ : Rel A c)
               → (A → B) → Set (a ℓ⊔ b ℓ⊔ c)
  NonInjective {A = A} _≈_ f
    = Σ (A × A) (λ { (x₁ , x₂) → ¬ (x₁ ≈ x₂) × f x₁ ≡ f x₂ })

  NonInjective-≡ : ∀{a b}{A : Set a}{B : Set b}
                 → (A → B) → Set (a ℓ⊔ b)
  NonInjective-≡ = NonInjective _≡_

  NonInjective-≡-preds : ∀{a b}{A : Set a}{B : Set b}{ℓ₁ ℓ₂ : Level}
                      → (A → Set ℓ₁)
                      → (A → Set ℓ₂)
                      → (A → B) → Set (a ℓ⊔ b ℓ⊔ ℓ₁ ℓ⊔ ℓ₂)
  NonInjective-≡-preds Pred1 Pred2 f = Σ (NonInjective _≡_ f) λ { ((a₀ , a₁) , _ , _) → Pred1 a₀ × Pred2 a₁ }

  NonInjective-≡-pred : ∀{a b}{A : Set a}{B : Set b}{ℓ : Level}
                      → (P : A → Set ℓ)
                      → (A → B) → Set (a ℓ⊔ b ℓ⊔ ℓ)
  NonInjective-≡-pred Pred = NonInjective-≡-preds Pred Pred

  NonInjective-∘ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
                 → {f : A → B}(g : B → C)
                 → NonInjective-≡  f
                 → NonInjective-≡ (g ∘ f)
  NonInjective-∘ g ((x0 , x1) , (x0≢x1 , fx0≡fx1))
    = ((x0 , x1) , x0≢x1 , (cong g fx0≡fx1))

  --------------------------------------------
  -- Handy fmap and bind for specific types --

  _<M$>_ : ∀{a b}{A : Set a}{B : Set b}
         → (f : A → B)
         → Maybe A → Maybe B
  _<M$>_ = Maybe-map

  <M$>-univ : ∀{a b}{A : Set a}{B : Set b}
            → (f : A → B)(x : Maybe A)
            → {y : B} → f <M$> x ≡ just y
            → ∃[ x' ] (x ≡ just x' × f x' ≡ y)
  <M$>-univ f (just x) refl = x , (refl , refl)

  maybe-lift : {A : Set}
             → {mx : Maybe A}{x : A}
             → (P : A → Set)
             → P x → mx ≡ just x
             → maybe {B = const Set} P ⊥ mx
  maybe-lift {mx = just .x} {x} P px refl = px

  <M$>-nothing : ∀ {a b}{A : Set a}{B : Set b}(f : A → B)
               → f <M$> nothing ≡ nothing
  <M$>-nothing _ = refl

  _<⊎$>_ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
         → (A → B) → C ⊎ A → C ⊎ B
  f <⊎$> (inj₁ hb) = inj₁ hb
  f <⊎$> (inj₂ x)  = inj₂ (f x)

  _⊎⟫=_ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
        → C ⊎ A → (A → C ⊎ B) → C ⊎ B
  (inj₁ x) ⊎⟫= _ = inj₁ x
  (inj₂ a) ⊎⟫= f = f a

  -- a non-dependent eliminator
  eitherS : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
            (x : Either A B) → ((x : A) → C) → ((x : B) → C) → C
  eitherS eab fa fb = case eab of λ where
    (Left  a) → fa a
    (Right b) → fb b

  open import Data.String as String
    hiding (_==_ ; _≟_ ; concat)

  check : Bool → List String → Either String Unit
  check b t = if b then inj₂ unit else inj₁ (String.intersperse "; " t)

  toWitnessT : ∀{ℓ}{P : Set ℓ}{d : Dec P} → ⌊ d ⌋ ≡ true → P
  toWitnessT {d = yes proof} _ = proof

  toWitnessF : ∀{ℓ}{P : Set ℓ}{d : Dec P} → ⌊ d ⌋ ≡ false → ¬ P
  toWitnessF{d = no proof} _ = proof

  Any-satisfied-∈ : ∀{a ℓ}{A : Set a}{P : A → Set ℓ}{xs : List A}
                  → Any P xs → Σ A (λ x → P x × x ∈ xs)
  Any-satisfied-∈ (here px) = _ , (px , here refl)
  Any-satisfied-∈ (there p) = let (a , px , prf) = Any-satisfied-∈ p
                               in (a , px , there prf)

  f-sum : ∀{a}{A : Set a} → (A → ℕ) → List A → ℕ
  f-sum f = sum ∘ List-map f

  maybeSMP : ∀ {ℓ} {A B : Set} {m : Set → Set ℓ} ⦃ _ : Monad m ⦄ → m (Maybe A) → B → (A → m B) → m B
  maybeSMP ma b f = do
    x ← ma
    case x of λ where
      nothing  → pure b
      (just j) → f j

  open import LibraBFT.Base.Util public

  -- Like a Haskell list-comprehension for ℕ : [ n | n <- [from .. to] ]
  fromToList : ℕ → ℕ → List ℕ
  fromToList from to with from ≤′? to
  ... | no ¬pr = []
  ... | yes pr = fromToList-le from to pr []
   where
    fromToList-le : ∀ (from to : ℕ) (klel : from ≤′ to) (acc : List ℕ) → List ℕ
    fromToList-le from ._        ≤′-refl       acc = from ∷ acc
    fromToList-le from (suc to) (≤′-step klel) acc = fromToList-le from to klel (suc to ∷ acc)

  _ : fromToList 1 1 ≡ 1 ∷ []
  _ = refl
  _ : fromToList 1 2 ≡ 1 ∷ 2 ∷ []
  _ = refl
  _ : fromToList 2 1 ≡ []
  _ = refl
