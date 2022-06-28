module Dijkstra.AST.Prelude where

open import Agda.Builtin.Unit
     public
open import Data.Bool                   using (Bool; true; false; not)
     public
open import Data.Sum
     using    (_⊎_ ; inj₁ ; inj₂)
     renaming ([_,_] to either)
open import Data.Sum.Properties
     using    (inj₂-injective)
     public
open import Data.Empty
     using    (⊥ ; ⊥-elim)
     public
open import Data.Empty
     renaming (⊥ to Void)
     public
open import Data.List                   using (List ; length ; [] ; _∷_ ; _++_)
     public
open import Data.Maybe                  using (Maybe ; maybe ; just ; nothing)
     public
open import Data.Maybe.Properties       using (just-injective)
     renaming (≡-dec to Maybe-≡-dec)
    public
open import Data.Product                using (_×_ ; _,_ ; proj₁ ; proj₂)
     public
open import Data.Unit.NonEta            using (Unit; unit)
     public
open import Function
     public
open import Level as Level
     renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
     public
import      Level.Literals as Level     using (#_)
open import Relation.Binary.PropositionalEquality
     public

-- NOTE: This function is defined to give extra documentation when discharging
-- absurd cases where Agda can tell by pattern matching that `A` is not
-- inhabited. For example:
-- > absurd (just v ≡ nothing) case impossibleProof of λ ()
infix 0 absurd_case_of_
absurd_case_of_ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) {B : Set ℓ₂} → A → (A → ⊥) → B
absurd A case x of f = ⊥-elim (f x)

Either : ∀ {a b} → Set a → Set b → Set (a ℓ⊔ b)
Either A B = A ⊎ B
pattern Left  x = inj₁ x
pattern Right x = inj₂ x
