open import LibraBFT.Prelude 
  hiding (lookup)
open import LibraBFT.Hash

module LibraBFT.Concrete.Util.HashSet {Key : Set}(hashK : Key → Hash) where

  postulate
    HashSet : Set 

    -- Predicates
    _∈HS_          : Hash → HashSet → Set
    ∈HS-irrelevant : (h : Hash)(hs : HashSet)
                   → (p₀ p₁ : h ∈HS hs) → p₀ ≡ p₁

    -- functionality
    empty          : HashSet
    lookup         : HashSet → Hash → Maybe Key
    _∈HS?_         : (h : Hash)(hs : HashSet)
                   → Dec (h ∈HS hs)
    hs-insert      : (k : Key)(hs : HashSet)
                   → lookup hs (hashK k) ≡ nothing
                   → HashSet

    -- properties
    ∈HS-empty-⊥ : ∀ {h} → h ∈HS empty → ⊥
{-
    -- properties
    ∈HS-correct : (k : Key)(hs : HashSet)
                → k ∈HS hs
                → lookup hs (hashK k) ≡ just k

    ∉HS-correct : (k : Key)(hs : HashSet)
                → ¬ k ∈HS hs
                → lookup hs (hashK k) ≢ just k

    lookup-correct : {k : Key}(h : Hash)(hs : HashSet)
                   → lookup hs h ≡ just k
                   → h ≡ hashK k  

    lookup-∈HS : {k : Key}(h : Hash)(hs : HashSet)
               → lookup hs h ≡ just k
               → k ∈HS hs

    hs-insert-∈HS : (k : Key)(hs : HashSet)
                  → (prf : lookup hs (hashK k) ≡ nothing)
                  → k ∈HS hs-insert k hs prf

    hs-insert-stable : ∀{k k' hs}
                     → (prf : lookup hs (hashK k) ≡ nothing)
                     → k' ∈HS hs
                     → k' ∈HS (hs-insert k hs prf)

    hs-insert-target : ∀{k k' hs}
                     → (prf : lookup hs (hashK k) ≡ nothing)
                     → ¬ (k' ∈HS hs)
                     → k' ∈HS (hs-insert k hs prf)
                     → k' ≡ k

-}
