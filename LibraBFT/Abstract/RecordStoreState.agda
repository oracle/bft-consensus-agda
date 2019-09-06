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

  -- A type 'RSS' is seen, by the abstract model, as a RecordStoreState
  -- if it contains a pool of unique records (hence the irrelevance cond.)
  record isRecordStoreState {a}(RSS : Set a) : Set (ℓ+1 a) where
    constructor rss
    field
      isInPool            : Record → Set
      isInPool-irrelevant : ∀{r}(p₀ p₁ : isInPool r) → p₀ ≡ p₁
  open isRecordStoreState public
