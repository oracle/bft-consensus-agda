open import LibraBFT.Prelude
  hiding (lookup)

module LibraBFT.Concrete.Util.KVMap  {ℓ} {Key : Set} {Val : Set ℓ} where

    postulate
      KVMap : Set ℓ

      -- functionality
      empty          : KVMap
      lookup         : KVMap → Key → Maybe Val
      kvm-insert     : (k : Key)(v : Val)(kvm : KVMap)
                     → lookup kvm k ≡ nothing
                     → KVMap

      -- properties
      lookup-correct : {k : Key}{v : Val}{kvm : KVMap}
                     → (prf : lookup kvm k ≡ nothing)
                     → lookup (kvm-insert k v kvm prf) k ≡ just v

      lookup-stable  : {k k' : Key}{v : Val}{kvm : KVMap}
                     → (prf : lookup kvm k ≡ nothing)
                     → lookup (kvm-insert k v kvm prf) k' ≡ just v
                     → lookup (kvm-insert k v kvm prf) k' ≡ just v

      insert-target  : ∀{k k' kvm v v'}
                     → (prf : lookup kvm k ≡ nothing)
                     → lookup kvm k' ≢ just v
                     → lookup (kvm-insert k v' kvm prf) k' ≡ just v
                     → k' ≡ k × v ≡ v'

      kvm-empty      : {k : Key} → lookup empty k ≡ nothing

      kvm-empty-⊥    : {k : Key} {v : Val} → lookup empty k ≡ just v → ⊥
