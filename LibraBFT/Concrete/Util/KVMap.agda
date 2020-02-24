open import LibraBFT.Prelude

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

   -- TODO: update properties to reflect kvm-update, consider combining insert/update
   kvm-update     : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → lookup k kvm ≢ nothing
                  → KVMap Key Val

   -- TODO: need properties relating kvm-toList to empty, kvm-insert and kvm-update
   kvm-size       : KVMap Key Val → ℕ
   kvm-toList     : KVMap Key Val → List (Key × Val)
   kvm-toList-length : (kvm : KVMap Key Val)
                     → length (kvm-toList kvm) ≡ kvm-size kvm

   -- TODO: need properties relating kvm-fromList showing that IF all keys in the
   -- supplied list are distinct, then all pairs are in the resulting map, and if
   -- not, we get nothing
   kvm-fromList   : List (Key × Val) → Maybe (KVMap Key Val)

   -- properties
   lookup-correct : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k (kvm-insert k v kvm prf) ≡ just v

   lookup-stable  : {kvm : KVMap Key Val}{k k' : Key}{v' : Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≡ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v

   insert-target  : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≢ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v
                  → k' ≡ k × v ≡ v'

   kvm-empty      : lookup {Val = Val} k empty ≡ nothing

   kvm-empty-⊥    : {k : Key} {v : Val} → lookup k empty ≡ just v → ⊥



  -- Corollary
 lookup-stable-1  : {kvm : KVMap Key Val}{k k' : Key}{v' : Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≡ just v'
                  → lookup k' (kvm-insert k v kvm prf) ≡ lookup k' kvm
 lookup-stable-1 prf hyp = trans (lookup-stable prf hyp) (sym hyp)

