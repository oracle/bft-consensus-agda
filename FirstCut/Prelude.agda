module Prelude where
  
  open import Data.Empty public 

  open import Data.Nat public
  
  open import Data.List public

  open import Data.List.Any
    using (Any; here; there)
    public
  
  open import Data.Vec
    using (Vec; []; _∷_)
    public
  
  open import Data.Maybe
    using (Maybe; just; nothing)
    public
  
  open import Data.Fin
    using (Fin; suc; zero)
    renaming (_<_ to _<Fin_)
    public
  
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; _≢_)
    public
  
  open import Data.Sum
    using (_⊎_; inj₁; inj₂)
    public
  
  open import Function
    using (_∘_)
    public

  open import Data.Product
    using (Σ; ∃-syntax; _×_; _,_)
    public
 
  open import Relation.Unary
    hiding (Irrelevant)
    public

  open import Relation.Nullary
    public
