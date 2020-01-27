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

   lookup         : Key → KVMap Key Val → Maybe Val
   kvm-insert     : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → lookup k kvm ≡ nothing
                  → KVMap Key Val

   -- properties
   lookup-correct : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k (kvm-insert k v kvm prf) ≡ just v

   lookup-stable  : {kvm : KVMap Key Val}{k k' : Key}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≡ just v
                  → lookup k' (kvm-insert k v kvm prf) ≡ just v

   insert-target  : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≢ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v
                  → k' ≡ k × v ≡ v'

   kvm-empty      : lookup {Val = Val} k empty ≡ nothing

   kvm-empty-⊥    : {k : Key} {v : Val} → lookup k empty ≡ just v → ⊥
