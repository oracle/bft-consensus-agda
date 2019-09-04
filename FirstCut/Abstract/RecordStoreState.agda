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
  open import Abstract.Records ec hash hash-cr
  open import Abstract.RecordChain ec hash hash-cr
  
  postulate _∈_ : ∀{a}{A : Set a} → A → List A → Set

  record RecordStoreState : Set₁ where
    constructor rss
    field
      pool       : List Record
      correct    : (r : Record) → r ∈ pool → WithPool.RecordChain (_∈ pool) r
  open RecordStoreState public
{-

  module RecordChainForRSS (curr : RecordStoreState) where
    open WithPool (_∈ pool curr) public
-}
{-

  RecordChain : RecordStoreState → Record → Set₁
  RecordChain curr r = WithPool.RecordChain (_∈ pool curr) r
      
  𝕂-chain : {curr : RecordStoreState} 
          → ℕ → ∀ {r} → RecordChain curr r → Set₁
  𝕂-chain {curr} k rc = WithPool.𝕂-chain (_∈ pool curr) k rc
-}

{- 

  FinishesWith : Record → ∃ (λ r → RecordChain r) → Set₁
  FinishesWith r (r' , _) = r ≡ r'

  Validated : RecordStoreState → Record → Set₁
  Validated (rss chains) r = Any (FinishesWith r) chains

-}
