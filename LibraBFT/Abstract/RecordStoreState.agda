open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

open import LibraBFT.Abstract.EpochConfig

module LibraBFT.Abstract.RecordStoreState {f : ℕ} (ec : EpochConfig f) 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Abstract.Records ec 

  -- TODO: Abstract away from lists and let the implemnter choose!
  record isRecordStoreState {a}(RSS : Set a) : Set (ℓ+1 a) where
    constructor rss
    field
      isInPool            : Record → Set
      isInPool-irrelevant : ∀{r}(p₀ p₁ : isInPool r) → p₀ ≡ p₁
  open isRecordStoreState public

  {- Make the record above into a abstract interface:

  RecordStoreState : Set₂ -- 𝓡
  RecordStoreState = Σ (P : Record → Set)
                       (λ pool → ∀ r → r ∈ pool → WithPool.RecordChain (_∈ pool) ∈-irrelevant r)

  abstractRSS : Concrete.RecordStoreState → Abstract.RecordStoreState
  abstractRSS ...

  abstract-is-ok : ∀{r}{crss : Concrete.RecordStoreState} → r ∈ crss → r ∈ (abstractRSS crss)
 
  algoRSS : 𝓡
  algoRSS = ...

  insertNetworkRecord : Concrete.Record → Concrete.RecordStoreState → Concrete.RecordStoreState
  insertNetworkRecord = ...

  inr-respects-irh : ∀{current nr} 
                   → IncreasingRoundRule (abstractRSS current)
                   → IncreasingRoundRule (abstractRSS (insertNetworkRecord nr current))
  -}
  
