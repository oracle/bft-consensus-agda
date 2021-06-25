{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
-- This is a selection of useful functions and definitions
-- from the standard library that we tend to use a lot.
module LibraBFT.Prelude where

  open import Level
    renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
    public

  1ℓ : Level
  1ℓ = ℓ+1 0ℓ

  open import Agda.Builtin.Unit
    public

  open import Function
    using (_∘_; id; case_of_; _on_; typeOf; flip; const; _∋_)
    public

  infixl 1 _&_
  _&_ = Function._|>_

  open import Data.Unit.NonEta
    public

  open import Data.Empty
    public

  open import Data.Nat
    renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
    public

  open import Data.Nat.Properties
    hiding (≡-irrelevant)
    public

  open import Data.List
    renaming (map to List-map ; filter to List-filter ; lookup to List-lookup;
              tabulate to List-tabulate)
    hiding (fromMaybe; [_])
    public

  open import Data.List.Properties
    renaming (≡-dec to List-≡-dec; length-map to List-length-map; map-compose to List-map-compose)
    using (∷-injective; length-++; map-++-commute; sum-++-commute; map-tabulate; ++-identityʳ)
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
             )
    public

  open import Data.List.Relation.Unary.All
    using (All; []; _∷_)
    renaming (head to All-head; tail to All-tail;
              lookup to All-lookup; tabulate to All-tabulate;
              reduce to All-reduce)
    public

  open import Data.List.Relation.Unary.All.Properties
    renaming ( tabulate⁻ to All-tabulate⁻
             ; tabulate⁺ to All-tabulate⁺
             ; map⁺      to All-map⁺
             ; map⁻      to All-map⁻
             )
    public

  open import Data.List.Membership.Propositional
    using (_∈_; _∉_)
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
    hiding (_≤?_; _<_; _<?_; _≤_)
    public

  open import Data.Maybe
    renaming (map to Maybe-map; zip to Maybe-zip ; _>>=_ to _Maybe->>=_)
    hiding (align; alignWith; zipWith)
    public

  maybeS : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
           (x : Maybe A) → B nothing → ((x : A) → B (just x)) → B x
  maybeS {B = B} x f t = maybe {B = B} t f x

  open import Data.Maybe.Relation.Unary.Any
    renaming (Any to Maybe-Any; dec to Maybe-Any-dec)
    hiding (map; zip; zipWith; unzip ; unzipWith)
    public

  maybe-any-⊥ : ∀{a}{A : Set a} → Maybe-Any {A = A} (λ _ → ⊤) nothing → ⊥
  maybe-any-⊥ ()

  open import Data.Maybe.Properties
    using (just-injective)
    renaming (≡-dec to Maybe-≡-dec)
    public

  open import Data.Fin
    using (Fin; suc; zero; fromℕ; fromℕ< ; toℕ ; cast)
    renaming (_≟_ to _≟Fin_; _≤?_ to _≤?Fin_; _≤_ to _≤Fin_ ; _<_ to _<Fin_;
              inject₁ to Fin-inject₁; inject+ to Fin-inject+)
    public

  fins : (n : ℕ) → List (Fin n)
  fins n = Vec-toList (Vec-allFin n)

  open import Data.Fin.Properties
    using (toℕ-injective)
    renaming (<-cmp to Fin-<-cmp; <⇒≢ to <⇒≢Fin)
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
    renaming ([_,_] to either; map to ⊎-map; map₂ to ⊎-map₂)
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

  -- Evidence that a function is not injective
  NonInjective : ∀{a b c}{A : Set a}{B : Set b}
               → (_≈_ : Rel A c)
               → (A → B) → Set (a ℓ⊔ b ℓ⊔ c)
  NonInjective {A = A} _≈_ f
    = Σ (A × A) (λ { (x₁ , x₂) → ¬ (x₁ ≈ x₂) × f x₁ ≡ f x₂ })

  NonInjective-≡ : ∀{a b}{A : Set a}{B : Set b}
                 → (A → B) → Set (a ℓ⊔ b)
  NonInjective-≡ = NonInjective _≡_

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

  -- Syntactic support for more faithful model of Haskell code
  Either : ∀ {a b} → Set a → Set b → Set (a ℓ⊔ b)
  Either A B = A ⊎ B
  pattern Left  x = inj₁ x
  pattern Right x = inj₂ x

  open import Data.String as String
    hiding (_==_)

  check : Bool → List String → Either String Unit
  check b t = if b then inj₂ unit else inj₁ (String.intersperse "; " t)

  record Eq {ℓ : Level} (A : Set ℓ) : Set ℓ where
    infix 4 _==_
    field
      _==_ : (a b : A) → Dec (a ≡ b)
  open Eq ⦃ ... ⦄ public

  instance
    Eq-Nat : Eq ℕ
    Eq._==_ Eq-Nat = _≟ℕ_

    -- TODO-1: Data.Maybe.Relation.Binary.Pointwise
    Eq-Maybe : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → Eq (Maybe A)
    (Eq-Maybe Eq.== nothing) nothing = yes refl
    (Eq-Maybe Eq.== nothing) (just x) = no λ where ()
    (Eq-Maybe Eq.== just x) nothing = no λ where ()
    (Eq-Maybe Eq.== just a) (just b)
      with a == b
    ... | no  proof = no (λ where refl → proof refl)
    ... | yes proof = yes (cong just proof)

  -- TODO-1: Maybe this belongs somewhere else?  It's in a similar
  -- category as Optics, so maybe should similarly be in a module that
  -- is separate from the main project?
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

  instance
    ToBool-Bool : ToBool Bool
    ToBool-Bool = record { toBool = id }

    ToBool-Dec : ∀{a}{A : Set a} → ToBool (Dec A)
    ToBool-Dec = record { toBool = ⌊_⌋ }

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

  Any-satisfied-∈ : ∀{a ℓ}{A : Set a}{P : A → Set ℓ}{xs : List A}
                  → Any P xs → Σ A (λ x → P x × x ∈ xs)
  Any-satisfied-∈ (here px) = _ , (px , here refl)
  Any-satisfied-∈ (there p) = let (a , px , prf) = Any-satisfied-∈ p
                               in (a , px , there prf)

  f-sum : ∀{a}{A : Set a} → (A → ℕ) → List A → ℕ
  f-sum f = sum ∘ List-map f

  record Monad {ℓ₁ ℓ₂ : Level} (M : Set ℓ₁ → Set ℓ₂) : Set (ℓ₂ ℓ⊔ ℓ+1 ℓ₁) where
    infixl 1 _>>=_ _>>_
    field
      return : ∀ {A : Set ℓ₁} → A → M A
      _>>=_  : ∀ {A B : Set ℓ₁} → M A → (A → M B) → M B

    _>>_ : ∀ {A B : Set ℓ₁} → M A → M B → M B
    m₁ >> m₂ = m₁ >>= λ _ → m₂

  open Monad ⦃ ... ⦄ public

  open import Category.Monad
  import      Data.Sum.Categorical.Left
  instance
    Monad-Error : ∀ {ℓ}{C : Set ℓ} → Monad{ℓ}{ℓ} (Either C)
    Monad.return (Monad-Error{ℓ}{C}) = RawMonad.return (Data.Sum.Categorical.Left.monad C ℓ)
    Monad._>>=_ (Monad-Error{ℓ}{C}) = RawMonad._>>=_ (Data.Sum.Categorical.Left.monad C ℓ)

  open import LibraBFT.Base.Util public
