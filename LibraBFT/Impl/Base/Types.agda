{- TODO: copyright -}


module LibraBFT.Impl.Base.Types where

  open import LibraBFT.Prelude
  open import LibraBFT.Hash

  NodeId : Set
  NodeId = ℕ

  UID : Set
  UID = Hash

  _≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁)
  _≟UID_ = _≟Hash_
