open import LibraBFT.Prelude
open import LibraBFT.Lemmas

module LibraBFT.Hash where


 -------------------------------------------------
 -- Hash function postulates
 --
 -- We are now assuming that our 'auth' function is collision
 -- resistant. We might be able to carry the full proof in agda,
 -- but that can take place on another module.


 -- We define a ByteString as a list of bits
 ByteString : Set
 ByteString = List Bool

 dummyByteString : ByteString
 dummyByteString = replicate 32 false

 Hash : Set
 Hash = Σ ByteString (λ bs → length bs ≡ 32)

 dummyHash : Hash
 dummyHash = (dummyByteString , refl)

 _≟Hash_ : (h₁ h₂ : Hash) → Dec (h₁ ≡ h₂)
 (l , pl) ≟Hash (m , pm) with List-≡-dec _≟Bool_ l m
 ...| yes refl = yes (cong (_,_ l) (≡-pi pl pm))
 ...| no  abs  = no (abs ∘ ,-injectiveˡ)

 encodeH : Hash → ByteString
 encodeH (bs , _) = bs

 encodeH-inj : ∀ i j → encodeH i ≡ encodeH j → i ≡ j
 encodeH-inj (i , pi) (j , pj) refl = cong (_,_ i) (≡-pi pi pj)

 encodeH-len : ∀{h} → length (encodeH h) ≡ 32
 encodeH-len { bs , p } = p

 postulate
   -- Encoding and decoding
   encodeℕ : ℕ   → ByteString

   -- Encodings have always the same size! (these could be any constant, really)
   encodeℕ-len : ∀{n} → length (encodeℕ n) ≡ 8

   -- Encodings are injections
   encodeℕ-inj : ∀ i j → encodeℕ i ≡ encodeℕ j → i ≡ j

 -- Naturally, if the size of the encoding is fixed by the type, it is always the same!
 encodeℕ-len-lemma : ∀ i j → length (encodeℕ i) ≡ length (encodeℕ j)
 encodeℕ-len-lemma i j = trans (encodeℕ-len {i}) (sym (encodeℕ-len {j}))

 encodeH-len-lemma : ∀ i j → length (encodeH i) ≡ length (encodeH j)
 encodeH-len-lemma i j = trans (encodeH-len {i}) (sym (encodeH-len {j}))

 -- Which means that we can make a helper function that combines
 -- the necessary injections into one big injection
 ++b-2-inj : (h₁ h₂ : Hash){l₁ l₂ : Hash}
           → encodeH h₁ ++ encodeH l₁
              ≡ encodeH h₂ ++ encodeH l₂
           → h₁ ≡ h₂ × l₁ ≡ l₂
 ++b-2-inj h₁ h₂ {l₁} {l₂} hip
   with ++-inj {m = encodeH h₁} {n = encodeH h₂} (encodeH-len-lemma h₁ h₂) hip
 ...| hh , ll = encodeH-inj h₁ h₂ hh , encodeH-inj l₁ l₂ ll 

 Collision : {A B : Set}(f : A → B)(a₁ a₂ : A) → Set
 Collision f a₁ a₂ = a₁ ≢ a₂ × f a₁ ≡ f a₂

 module WithCryptoHash
   -- A Hash function maps a bytestring into a hash.
   (hash    : ByteString → Hash)
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y) where

  HashBroke : Set
  HashBroke = Σ ( ByteString × ByteString ) (λ { (x₁ , x₂) → Collision hash x₁ x₂ })

  -- We define the concatenation of hashes like one would expect
  hash-concat : List Hash  → Hash
  hash-concat l = hash (concat (List-map encodeH l))

  -- And voila, it is either injective ot we broke the hash function!
  hash-concat-inj : ∀{l₁ l₂} → hash-concat l₁ ≡ hash-concat l₂ → HashBroke ⊎ l₁ ≡ l₂
  hash-concat-inj {[]} {x ∷ xs} h with hash-cr h
  ...| inj₁ col = inj₁ (([] , encodeH x ++ foldr _++_ [] (List-map encodeH xs)) , col)
  ...| inj₂ abs = ⊥-elim (++-abs (encodeH x) (subst (_≤_ 1) (sym (encodeH-len {x})) (s≤s z≤n)) abs)
  hash-concat-inj {x ∷ xs} {[]} h with hash-cr h
  ...| inj₁ col = inj₁ ((encodeH x ++ foldr _++_ [] (List-map encodeH xs) , []) , col)
  ...| inj₂ abs = ⊥-elim (++-abs (encodeH x) (subst (_≤_ 1) (sym (encodeH-len {x})) (s≤s z≤n)) (sym abs))
  hash-concat-inj {[]}    {[]} h = inj₂ refl
  hash-concat-inj {x ∷ xs} {y ∷ ys} h with hash-cr h
  ...| inj₁ col = inj₁ ((encodeH x ++ foldr _++_ [] (List-map encodeH xs) , encodeH y ++ foldr _++_ [] (List-map encodeH ys)) , col)
  ...| inj₂ res  with ++-inj {m = encodeH x} {n = encodeH y} (encodeH-len-lemma x y) res
  ...| xy , xsys with hash-concat-inj {l₁ = xs} {l₂ = ys} (cong hash xsys)
  ...| inj₁ hb    = inj₁ hb
  ...| inj₂ final = inj₂ (cong₂ _∷_ (encodeH-inj x y xy) final)

