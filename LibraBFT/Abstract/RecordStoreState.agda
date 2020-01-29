open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.RecordStoreState 
    (ec  : EpochConfig)
    (UID : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
 where

  open import LibraBFT.Abstract.Records ec UID _≟UID_

  -- A type 'RSS' is seen, by the abstract model, as a RecordStoreState
  -- if it contains a pool of unique records (hence the irrelevance cond.)
  record isRecordStoreState {a}(RSS : Set a) : Set (ℓ+1 a) where
    field
      isInPool            : Record → RSS → Set
      isInPool-irrelevant : ∀{r st}(p₀ p₁ : isInPool r st) → p₀ ≡ p₁
  open isRecordStoreState public
 
