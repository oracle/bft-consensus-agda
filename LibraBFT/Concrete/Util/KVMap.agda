open import LibraBFT.Prelude
  hiding (lookup)

module LibraBFT.Concrete.Util.KVMap  where

 variable
   Key : Set 
   Val : Set

   k k' : Key
   v v' : Val
   

 postulate
   KVMap : Set → Set → Set 

   _∈KV_          : Key → KVMap Key Val → Set
   _∈KV?_         : (k : Key) (kvm : KVMap Key Val) → Dec (k ∈KV kvm)
   ∈KV-irrelevant : (k : Key) (kvm : KVMap Key Val)
                  → (r s : k ∈KV kvm)
                  → r ≡ s 

   -- functionality
   empty          : KVMap Key Val

   ∈KV-empty-⊥    : k ∈KV (empty {Val = Val}) → ⊥

   lookup         : KVMap Key Val → Key → Maybe Val
   kvm-insert     : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → lookup kvm k ≡ nothing
                  → KVMap Key Val

   -- properties
   lookup-correct : {kvm : KVMap Key Val}
                  → (prf : lookup kvm k ≡ nothing)
                  → lookup (kvm-insert k v kvm prf) k ≡ just v

   lookup-stable  : {kvm : KVMap Key Val}
                  → (prf : lookup kvm k ≡ nothing)
                  → lookup (kvm-insert k v kvm prf) k' ≡ just v
                  → lookup (kvm-insert k v kvm prf) k' ≡ just v

   insert-target  : {kvm : KVMap Key Val}
                  → (prf : lookup kvm k ≡ nothing)
                  → lookup kvm k' ≢ just v
                  → lookup (kvm-insert k v' kvm prf) k' ≡ just v
                  → k' ≡ k × v ≡ v'

   kvm-empty      : lookup {Val = Val} empty k ≡ nothing

   kvm-empty-⊥    : {k : Key} {v : Val} → lookup empty k ≡ just v → ⊥
