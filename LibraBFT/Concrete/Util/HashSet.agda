open import LibraBFT.Prelude 
  hiding (lookup)
open import LibraBFT.Hash

module LibraBFT.Concrete.Util.HashSet {Key : Set}(hashK : Key → Hash) where

  postulate
    HashSet : Set 

    -- Predicates
    _∈HS_          : (k : Key) → HashSet → Set
    ∈HS-irrelevant : (k : Key)(hs : HashSet)
                   → (p₀ p₁ : k ∈HS hs) → p₀ ≡ p₁

    -- functionality
    empty          : HashSet
    lookup         : HashSet → Hash → Maybe Key
    _∈HS?_         : (k : Key)(h : HashSet)
                   → Dec (k ∈HS h) 
    hs-insert      : HashSet → Key → HashSet

    -- properties
    lookup-correct : (k : Key)(hs : HashSet)
                   → k ∈HS hs
                   → lookup hs (hashK k) ≡ just k

    lookup-correct' : {k : Key}(h : Hash)(hs : HashSet)
                    → lookup hs h ≡ just k
                    → h ≡ hashK k  

    lookup-correct'' : {k : Key}(h : Hash)(hs : HashSet)
                     → lookup hs h ≡ just k
                     → k ∈HS hs

    hs-insert-stable : ∀{k k' hs}
                     → k' ∈HS hs
                     → k' ∈HS (hs-insert hs k)
                  
    hs-insert-target : ∀{k k' hs}
                     → ¬ (k' ∈HS hs)
                     → k' ∈HS (hs-insert hs k)
                     → k' ≡ k

    ∈HS-empty-⊥ : {k : Key} → k ∈HS empty → ⊥
