module Prelude where
  open import Data.Nat public
  open import Data.List public
  open import Data.Vec
    using (Vec; []; _∷_)
    public
  open import Data.Maybe
    using (Maybe; just; nothing)
    public
  open import Data.Fin
    using (Fin; suc; zero)
    public
  open import Relation.Binary.PropositionalEquality
    using (_≡_)
    public
  open import Data.Sum
    using (_⊎_; inj₁; inj₂)
    public
  open import Function
    using (_∘_)
    public
