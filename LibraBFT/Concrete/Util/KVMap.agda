open import LibraBFT.Prelude

module LibraBFT.Concrete.Util.KVMap  where

 variable
   Key : Set 
   Val : Set

   k k' : Key
   v v' : Val
   

 postulate
   -- TODO: It should be possible to instantiate the module with a Key type and provide this, but I
   -- don't understand the "variable" declaration above, or why we use it, and can't seem to make
   -- this work other than by postulating it
   _≟Key_ : ∀ (k1 k2 : Key) → Dec (k1 ≡ k2)

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

   update-target-≢  : {kvm : KVMap Key Val}
                  → ∀ {k1 k2 x}
                  → k2 ≢ k1
                  → lookup k1 kvm ≡ lookup k1 (kvm-update k2 v kvm x)

   kvm-empty      : lookup {Val = Val} k empty ≡ nothing

   kvm-empty-⊥    : {k : Key} {v : Val} → lookup k empty ≡ just v → ⊥

   KVM-extensionality : ∀ {kvm1 kvm2 : KVMap Key Val}
                      → (∀ (x : Key) → lookup x kvm1 ≡ lookup x kvm2)
                      → kvm1 ≡ kvm2


  -- Corollaries
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


 update-target  : {kvm : KVMap Key Val}
                → ∀ {k1 k2 x}
                → lookup k1 kvm ≢ lookup k1 (kvm-update k2 v kvm x)
                → k2 ≡ k1
 update-target {kvm = kvm}{k1 = k1}{k2 = k2}{x} vneq
    with k1 ≟Key k2
 ...| yes refl = refl
 ...| no  neq  = ⊥-elim (vneq (update-target-≢ {k1 = k1} {k2 = k2} (neq ∘ sym)))

 lookup-correct-update-3 : ∀ {kvm : KVMap Key Val}{k1 k2 v2}
                → (prf : lookup k2 kvm ≢ nothing)
                → lookup k2 kvm ≡ just v2
                → lookup k1 (kvm-update k2 v2 kvm prf) ≡ lookup k1 kvm
 lookup-correct-update-3 {kvm = kvm} {k1 = k1} {k2 = k2} {v2 = v2} prf with k1 ≟Key k2
 ...| yes refl = λ pr → trans (lookup-correct-update {v = v2} prf) (sym pr)
 ...| no  neq  = λ pr → sym (update-target-≢ {k1 = k1} {k2 = k2} {prf} λ k2≢k1 → ⊥-elim (neq (sym k2≢k1)))

 lookup-correct-update-4
                : ∀ {orig : KVMap Key Val}{k1}{v1}
                    {rdy : lookup k1 orig ≢ nothing}
                → lookup k1 orig ≡ just v1
                → kvm-update k1 v1 orig rdy ≡ orig
 lookup-correct-update-4 {orig = orig} {k1 = k1} {v1 = v1} {rdy = rdy} hyp =
    KVM-extensionality {kvm1 = kvm-update k1 v1 orig rdy} {kvm2 = orig}
                       λ x → lookup-correct-update-3 rdy hyp


