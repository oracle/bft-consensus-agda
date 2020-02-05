-- This is a selection of useful function
-- from the standard library that we tend to use a lot.
module LibraBFT.Prelude where

  open import Level
    renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
    public
  
  open import Agda.Builtin.Unit
    public

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
    renaming (map to List-map)
    hiding (fromMaybe; [_])
    public

  open import Data.List.Properties 
    renaming (≡-dec to List-≡-dec)
    using (∷-injective)
    public

  open import Data.List.Relation.Unary.Any
    using (Any; here; there)
    renaming (lookup to Any-lookup; map to Any-map)
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
    using (_∈_)
    public 

  open import Data.Vec
    using (Vec; []; _∷_)
    public
  
  open import Data.List.Relation.Pointwise 
    using (decidable-≡)
    public

  open import Data.Bool 
    renaming (_≟_ to _≟Bool_)
    hiding (_≤?_; _<_; _<?_; _≤_; T)
    public

  open import Data.Maybe 
    renaming (map to Maybe-map; zip to Maybe-zip)
    hiding (align; alignWith; zipWith)
    public

  open import Data.Maybe.Relation.Unary.Any
    renaming (Any to Maybe-Any; dec to Maybe-Any-dec)
    hiding (map; zip; zipWith; unzip ; unzipWith)
    public

  open import Data.Maybe.Properties
    using (just-injective)
    public

  open import Data.Fin
    using (Fin; suc; zero; fromℕ≤)
    renaming (_≤_ to _≤Fin_ ; _<_ to _<Fin_; inject₁ to Fin-inject₁)
    public
  
  open import Relation.Binary.PropositionalEquality
    hiding (decSetoid)
    public

  open import Relation.Binary.Core
    public

  ≡-irrelevant : ∀{a}{A : Set a} → Irrelevant {a} {A} _≡_
  ≡-irrelevant refl refl = refl
  
  open import Data.Sum
    public
  
  open import Function
    using (_∘_)
    public

  open import Data.Product
    renaming (map to split; swap to ×-swap)
    hiding (map₁; map₂; zip)
    public

  open import Data.Product.Properties
    public
 
--  open import Relation.Unary
--    hiding (Irrelevant; _⇒_)
--    public

  open import Relation.Nullary
    hiding (Irrelevant)
    public

  open import Relation.Nullary.Negation
    using (contradiction)
    public

  open import Relation.Binary
    using (Setoid)
    public

  -- We define a ByteString as a list of bits
  ByteString : Set
  ByteString = List Bool

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
