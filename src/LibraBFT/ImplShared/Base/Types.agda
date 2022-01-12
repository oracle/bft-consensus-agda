{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module LibraBFT.ImplShared.Base.Types where
  open import Util.Hash
  open import Util.Prelude

  NodeId : Set
  NodeId = ℕ

  _≟NodeId_ : (n1 n2 : NodeId) → Dec (n1 ≡ n2)
  _≟NodeId_ = _≟ℕ_

  UID : Set
  UID = Hash

  _≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁)
  _≟UID_ = _≟Hash_

  -- Just in case RoundManager is at a higher level in future
  ℓ-RoundManager : Level
  ℓ-RoundManager = 0ℓ

  ℓ-VSFP : Level
  ℓ-VSFP = 1ℓ ℓ⊔ ℓ-RoundManager
