open import Hash
open import BasicTypes
open import Prelude

open import Data.Nat.Properties

module Abstract.RecordStoreState {f : ℕ} (ec : EpochConfig f) 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open WithCryptoHash hash hash-cr
  open import Abstract.Records ec
  open import Abstract.RecordChain ec hash hash-cr
  
  postulate _∈_ : ∀{a}{A : Set a} → A → List A → Set
  
  AllValid : List Record → ∀{r} → RecordChain r → Set
  AllValid _ _ = Unit -- TODO: Write a predicate that ensures that all records in said recordchain are
                      --       valid with respect to the given list


  record RecordStoreState : Set₁ where
    constructor rss
    field
      valids  : List Record
      correct : (r : Record) → r ∈ valids → Σ (RecordChain r) (AllValid valids) 
      

{- 

  FinishesWith : Record → ∃ (λ r → RecordChain r) → Set₁
  FinishesWith r (r' , _) = r ≡ r'

  Validated : RecordStoreState → Record → Set₁
  Validated (rss chains) r = Any (FinishesWith r) chains

-}
