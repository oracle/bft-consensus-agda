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

   -- TODO: need properties showing that the resulting map contains (k , v) for
   --       each pair in the list, provided there is no pair (k , v') in the list
   --       after (k , v).  This is consistent with Haskell's Data.Map.fromList
   kvm-fromList   : List (Key × Val) → KVMap Key Val

   -- properties
   lookup-correct : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k (kvm-insert k v kvm prf) ≡ just v

   lookup-correct-update
                  : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≢ nothing)
                  → lookup k (kvm-update k v kvm prf) ≡ just v

   lookup-stable  : {kvm : KVMap Key Val}{k k' : Key}{v' : Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≡ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v

   insert-target-0 : {kvm : KVMap Key Val}
                   → {prf : lookup k kvm ≡ nothing}
                   → lookup k' kvm ≢ lookup k' (kvm-insert k v kvm prf)
                   → k ≡ k'

   insert-target  : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≢ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v
                  → k' ≡ k × v ≡ v'

   update-target  : {kvm : KVMap Key Val}
                  → ∀ {k1 k2 x}
                  → lookup k1 kvm ≢ lookup k1 (kvm-update k2 v kvm x)
                  → k2 ≡ k1

   kvm-empty      : lookup {Val = Val} k empty ≡ nothing

   kvm-empty-⊥    : {k : Key} {v : Val} → lookup k empty ≡ just v → ⊥



  -- Corollary
 lookup-stable-1  : {kvm : KVMap Key Val}{k k' : Key}{v' : Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≡ just v'
                  → lookup k' (kvm-insert k v kvm prf) ≡ lookup k' kvm
 lookup-stable-1 prf hyp = trans (lookup-stable prf hyp) (sym hyp)

 lookup-correct-update-2
                : {kvm : KVMap Key Val}
                → (prf : lookup k kvm ≢ nothing)
                → lookup k (kvm-update k v kvm prf) ≡ just v'
                → v ≡ v'
 lookup-correct-update-2 {kvm} prf lkup =
   just-injective
     (trans (sym (lookup-correct-update prf)) lkup)

 postulate
   -- Corollary
  lookup-stable-2  : {kvm : KVMap Key Val}{k k' : Key}{v' : Val}
                   → (prf : lookup k kvm ≡ nothing)
                   → lookup k' (kvm-insert k v kvm prf) ≡ just v'
                   → k' ≢ k
                   → lookup k' kvm ≡ just v'

