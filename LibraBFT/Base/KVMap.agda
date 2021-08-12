{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

-- This module contains a model of a key-value store, along with its
-- functionality and various properties about it.  Most of the properties
-- are not currently used, but they are included here based on our
-- experience in other work, as we think many of them will be needed when
-- reasoning about an actual LibraBFT implementation.

-- Although we believe the assumptions here are reasonable, it is always
-- possible that we made a mistake in postulating one of the properties,
-- making it impossible to implement.  Thus, it would a useful contribution
-- to:
--
-- TODO-1: construct an actual implementation and provide and prove the
-- necessary properties to satisfy the requirements of this module
--
-- Note that this would require some work, but should be relatively
-- straightforward and requires only "local" changes.

module LibraBFT.Base.KVMap  where

 private
  variable
   Key : Set
   Val : Set

   k k' : Key
   v v' : Val


 postulate -- valid assumptions, but would be good to eliminate with a reference implementation (above)
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
   insert         : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → KVMap Key Val
   kvm-insert     : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → lookup k kvm ≡ nothing
                  → KVMap Key Val
   elems          : KVMap Key Val → List Val
   delete         : Key → KVMap Key Val → KVMap Key Val

   -- TODO-3: update properties to reflect kvm-update, consider combining insert/update
   kvm-update     : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → lookup k kvm ≢ nothing
                  → KVMap Key Val

   kvm-insert-Haskell
                  : (k : Key)(v : Val)(kvm : KVMap Key Val)
                  → KVMap Key Val

   kvm-member     : (k : Key) (kvm : KVMap Key Val)
                  → Bool

   kvm-size       : KVMap Key Val → ℕ
   -- TODO-1: add properties relating kvm-toList to empty, kvm-insert and kvm-update
   kvm-keys       : KVMap Key Val → List Key
   kvm-toList     : KVMap Key Val → List (Key × Val)
   kvm-toList-length : (kvm : KVMap Key Val)
                     → length (kvm-toList kvm) ≡ kvm-size kvm

   -- TODO-1: need properties showing that the resulting map contains (k , v) for
   --         each pair in the list, provided there is no pair (k , v') in the list
   --         after (k , v).  This is consistent with Haskell's Data.Map.fromList
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

   insert-target  : {kvm : KVMap Key Val}
                  → (prf : lookup k kvm ≡ nothing)
                  → lookup k' kvm ≢ just v
                  → lookup k' (kvm-insert k v' kvm prf) ≡ just v
                  → k' ≡ k × v ≡ v'

   insert-target-≢ : {kvm : KVMap Key Val}{k k' : Key}
                   → (prf : lookup k kvm ≡ nothing)
                   → k' ≢ k
                   → lookup k' kvm ≡ lookup k' (kvm-insert k v kvm prf)

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

 insert-target-0 : {kvm : KVMap Key Val}
                 → (prf : lookup k kvm ≡ nothing)
                 → lookup k' kvm ≢ lookup k' (kvm-insert k v kvm prf)
                 → k ≡ k'
 insert-target-0 {k = k} {k' = k'} prf lookups≢
    with k' ≟Key k
 ...| yes refl = refl
 ...| no  neq  = ⊥-elim (lookups≢ (insert-target-≢ prf neq))
