-- This is a selection of useful function
-- from the standard library that we tend to use a lot.
module LibraBFT.Prelude where

  open import Level
    renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
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

  open import Data.List.Any
    using (Any; here; there)
    renaming (lookup to Any-lookup)
    public

  open import Data.List.All
    using (All; []; _∷_)
    renaming (head to All-head; tail to All-tail)
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

  open import Data.Fin
    using (Fin; suc; zero)
    renaming (_≤_ to _≤Fin_ ; _<_ to _<Fin_)
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
