{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Util.ByteString
open import Util.Encode
open import Util.Prelude
open import Util.Lemmas

-- This module defines Hash functions, and related properties

module Util.Hash where

 -------------------------------------------------
 -- Hash function postulates
 --
 postulate -- valid assumption: hashes are some (unspecified) number of bytes
   hashNumBytes : ℕ

 Hash : Set
 Hash = Σ ByteString (λ bs → length bs ≡ hashNumBytes)

 hashLen-pi : ∀ {bs : ByteString} {n : ℕ } → (p1 p2 : length bs ≡ n) → p1 ≡ p2
 hashLen-pi {[]}    {.0} refl refl = refl
 hashLen-pi {h ∷ t} {.(suc (length t))} refl refl = refl

 sameBS⇒sameHash : ∀ {h1 h2 : Hash}
         → proj₁ h1 ≡ proj₁ h2
         → h1 ≡ h2
 sameBS⇒sameHash { h1a , h1b } { h2a , h2b } refl rewrite hashLen-pi {h2a} h1b h2b = refl

 _≟Hash_ : (h₁ h₂ : Hash) → Dec (h₁ ≡ h₂)
 (l , pl) ≟Hash (m , pm) with List-≡-dec (Vec-≡-dec _≟Bool_) l m
 ...| yes refl = yes (cong (_,_ l) (≡-pi pl pm))
 ...| no  abs  = no (abs ∘ ,-injectiveˡ)

 instance
   Eq-Hash : Eq Hash
   Eq._≟_ Eq-Hash = _≟Hash_

 encodeH : Hash → ByteString
 encodeH (bs , _) = bs

 encodeH-inj : ∀ i j → encodeH i ≡ encodeH j → i ≡ j
 encodeH-inj (i , pi) (j , pj) refl = cong (_,_ i) (≡-pi pi pj)

 encodeH-len : ∀{h} → length (encodeH h) ≡ hashNumBytes
 encodeH-len { bs , p } = p

 encodeH-len-lemma : ∀ i j → length (encodeH i) ≡ length (encodeH j)
 encodeH-len-lemma i j = trans (encodeH-len {i}) (sym (encodeH-len {j}))

 -- Which means that we can make a helper function that combines
 -- the necessary injections into one big injection
 ++b-2-inj : (h₁ h₂ : Hash){l₁ l₂ : Hash}
           → encodeH h₁ ++ encodeH l₁ ≡ encodeH h₂ ++ encodeH l₂
           → h₁ ≡ h₂ × l₁ ≡ l₂
 ++b-2-inj h₁ h₂ {l₁} {l₂} hip
   with ++-inj {m = encodeH h₁} {n = encodeH h₂} (encodeH-len-lemma h₁ h₂) hip
 ...| hh , ll = encodeH-inj h₁ h₂ hh , encodeH-inj l₁ l₂ ll

 Collision : {A B : Set}(f : A → B)(a₁ a₂ : A) → Set
 Collision f a₁ a₂ = a₁ ≢ a₂ × f a₁ ≡ f a₂

 instance
   enc-Hash : Encoder Hash
   enc-Hash = record
     { encode     = encodeH
     ; encode-inj = encodeH-inj _ _
     }

 module WithCryptoHash
   -- A Hash function maps a bytestring into a hash.
   (hash    : BitString → Hash)
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y) where

  -- We define the concatenation of hashes like one would expect
  hash-concat : List Hash  → Hash
  hash-concat l = hash (bs-concat (List-map encodeH l))

  -- And voila, it is either injective ot we broke the hash function!
  hash-concat-inj : ∀{l₁ l₂} → hash-concat l₁ ≡ hash-concat l₂ → NonInjective-≡ hash ⊎ l₁ ≡ l₂
  hash-concat-inj {l₁} {l₂} hyp with hash-cr hyp
  ...| inj₁ col  = inj₁ ((_ , _) , col)
  ...| inj₂ same with bs-concat-inj (List-map encodeH l₁) (List-map encodeH l₂) same
  ...| res = inj₂ (map-inj encodeH (encodeH-inj _ _) res)
    where
      map-inj : ∀{a b}{A : Set a}{B : Set b}(f : A → B)
              → (f-injective : ∀{a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂)
              → ∀{xs ys} → List-map f xs ≡ List-map f ys → xs ≡ ys
      map-inj f finj {[]} {[]} hyp = refl
      map-inj f finj {x ∷ xs} {y ∷ ys} hyp
        = cong₂ _∷_ (finj (proj₁ (∷-injective hyp)))
                    (map-inj f finj (proj₂ (∷-injective hyp)))
