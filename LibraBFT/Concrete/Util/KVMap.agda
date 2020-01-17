open import LibraBFT.Prelude 
  hiding (lookup)

module LibraBFT.Concrete.Util.KVMap {Key : Set}{Val : Set} where

  postulate
    KVMap : Set 

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

    kvm-empty-⊥    : {k : Key} {v : Val} → lookup empty k ≡ just v → ⊥
