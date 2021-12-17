{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

-- To enable reasoning about algorithms that concatenate
-- ByteStrings and pass the result to a cryptographic hash
-- function (as LibraBFT does), it is critical to have an
-- injective bitstring concat function ('bs-concat', below).
--
-- To see why, suppose we hash a data structure that contains two
-- fields of type ByteString by passing its fields to a hash
-- function like this:
--
-- > h : String -> String -> Hash
-- > h a b = hash (concat [a , b])
--
-- This function is /NOT/ collision resistant:
--
-- > h "xx" "x" == hash (concat ["xx" , "x"])
-- >            == hash "xxx"
-- >            == hash (concat ["x" , "xx"]) == h "x" "xx"
--
-- We cannot solve the problem simply by using an arbitrary field
-- separator, because an arbitrary ByteString might contain the
-- separator.  For example, if we define:
--
-- > h a b = hash (concat [ a , ";" , b ])
--
-- Then, we still have:
--
-- > h "x;x" "x" == h "x" "x;x"
--
-- Two possible approaches to defining an injective `concat`
-- function are:
--
-- 1) Use some length-prefixed encoding where we know the size of
-- each field. This approach will work in practice but we won't
-- be able to prove its injectivity for arbitrary ByteStrings in
-- Agda: Regardless of how many bytes we reserve for size
-- information, there are some inputs that require more.
--
-- 2) Encoding the arguments' list structure in the result of
-- concat; inverting the concat function then becomes parsing a
-- list of values. This approach is analogous to:
--
-- > concat : List ByteString -> BitString
-- > concat = serialize . toJSON
--
-- We take the second approach.
module LibraBFT.Base.ByteString where

  -- A BitString is a list of bits
  BitString : Set
  BitString = List Bool

  _≟BitString_ : (bs1 bs2 : BitString) → Dec (bs1 ≡ bs2)
  _≟BitString_ = List-≡-dec _≟Bool_

  -- A ByteString is a list of bytes
  ByteString : Set
  ByteString = List (Vec Bool 8)

  _≟ByteString_ : (bs1 bs2 : ByteString) → Dec (bs1 ≡ bs2)
  _≟ByteString_ = List-≡-dec (Vec-≡-dec _≟Bool_)

  -- Concatenates ByteString prepending '11' to each byte.
  toBitString-pad' : ByteString → BitString
  toBitString-pad' = concat ∘ List-map (λ v → true ∷ true ∷ Vec-toList v)

  -- Concatenates a ByteString distinguishing an empty list from a non-empty list
  toBitString-pad : ByteString → BitString
  toBitString-pad []       = false ∷ false ∷ []
  toBitString-pad (b ∷ bs) = true  ∷ false ∷ Vec-toList b ++ toBitString-pad' bs

  -- Here's our injective concat function for ByteString
  bs-concat : List ByteString -> BitString
  bs-concat = concat ∘ List-map toBitString-pad

  ------------------------------------------------------------------------------
  -- operations

  -- TODO-1: these are prefixed with "BS∙" because they conflict with the
  -- versions in List that are imported via Prelude.
  -- It is possible to rename the List versions when importing them
  -- but that will make a big diff of the following proofs that
  -- should (IF renaming is done) in a separate PR.
  postulate -- to prove these operations
    BS∙drop       : ℕ → ByteString → ByteString
    BS∙isPrefixOf : ByteString → ByteString → Bool
    BS∙length     : ByteString → ℕ

  -----------------------
  -- Injectivity Proof --
  -----------------------

  -- The proof is straightforward once we figure out the core reasoning principle:
  -- Any non-injective cases would be some variation on:
  --
  --         bs-concat ([a] ∷ c) ≡ bs-concat ([b₀ , b₁] ∷ d)
  --
  --    <==> toBitString-pad [a] ++ bs-concat c ≡ toBitString-pad [b₀ , b₁] ++ bs-concat d
  --
  --    <==> 1 1 a₀ ⋯ a₇ ++ bs-concat c ≡ 1 1 b₀₀ ‌⋯ b₀₇ 1 0 b₁₀ ⋯ b₁₇ ++ bs-concat d
  --
  --         { ++ is injective for same-length prefixes }
  --
  --    <==> aᵢ ≡ b₀ᵢ × bs-concat c ≡ 1 0 b₁₀ ⋯ b₁₇ ++ bs-concat d
  --
  --         { impossible,  bs-concat c is either empty or starts with 11 }
  --
  --    <==> ⊥
  --
  -- The actual Agda is a little more involved; but this covers the intuition.

  -- Appending two lists of the same length is injective.
  ++-len-injective : ∀{a}{A : Set a}(xs₀ ys₀ : List A){xs₁ ys₁ : List A}
               → length xs₀ ≡ length ys₀
               → xs₀ ++ xs₁ ≡ ys₀ ++ ys₁
               → xs₀ ≡ ys₀ × xs₁ ≡ ys₁
  ++-len-injective [] [] len hyp = refl , hyp
  ++-len-injective (x ∷ xs0) (y ∷ ys0) len hyp
    = let x≡y , tails≡ = ∷-injective hyp
          a , b = ++-len-injective xs0 ys0 (suc-injective len) tails≡
       in cong₂ _∷_ x≡y a , b

  Vec-toList-length : ∀{a n}{A : Set a}(x : Vec A n) → length (Vec-toList x) ≡ n
  Vec-toList-length []       = refl
  Vec-toList-length (_ ∷ xs) = cong suc (Vec-toList-length xs)

  Vec-toList-inj : ∀{a n}{A : Set a}{x y : Vec A n}
                 → Vec-toList x ≡ Vec-toList y → x ≡ y
  Vec-toList-inj {x = []}     {[]}     hyp = refl
  Vec-toList-inj {x = x ∷ xs} {y ∷ ys} hyp
    = let x≡y , xs≡ys = ∷-injective hyp
       in cong₂ _∷_ x≡y (Vec-toList-inj xs≡ys)

  -- In general, _++_ is not injective.  However, we can
  -- characterize it universally with a /Prefix/ property.
  data _≺_ {a}{A : Set a} : List A → List A → Set where
    z≺n : ∀{xs}      → [] ≺ xs
    s≺s : ∀{x xs ys} → xs ≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  -- Returns the tail of ys; after dropping the prefix xs.
  ≺-drop : ∀{a}{A : Set a}{xs ys : List A} → xs ≺ ys → List A
  ≺-drop {ys = ys} z≺n = ys
  ≺-drop (s≺s a)       = ≺-drop a

  ++-≺ : ∀{a}{A : Set a}(xs ws : List A){ys zs : List A}
       → xs ++ ys ≡ ws ++ zs
       → Σ (xs ≺ ws) (λ prf → ≺-drop prf ++ zs ≡ ys)
       ⊎ Σ (ws ≺ xs) (λ prf → ≺-drop prf ++ ys ≡ zs)
  ++-≺ [] ys hyp = inj₁ (z≺n , sym hyp)
  ++-≺ (x ∷ xs) [] hyp = inj₂ (z≺n , hyp)
  ++-≺ (x ∷ xs) (y ∷ ys) hyp
    with ∷-injective hyp
  ...| refl , xs≡ys
    with ++-≺ xs ys xs≡ys
  ...| inj₁ (ok , prf) = inj₁ (s≺s ok , prf)
  ...| inj₂ (ok , prf) = inj₂ (s≺s ok , prf)

  ≺-respects-++-len
    : ∀{a}{A : Set a}(xs₀ ys₀ : List A){xs₁ ys₁ : List A}
    → (p : (xs₀ ++ xs₁) ≺ (ys₀ ++ ys₁))
    → length xs₀ ≡ length ys₀
    → xs₀ ≡ ys₀ × Σ (xs₁ ≺ ys₁) (λ p' → ≺-drop p ≡ ≺-drop p')
  ≺-respects-++-len [] [] prf hyp = refl , (prf , refl)
  ≺-respects-++-len (x ∷ xs) (.x ∷ ys) (s≺s prf) hyp
    with ≺-respects-++-len xs ys prf (suc-injective hyp)
  ...| xs≡ys , res , ok = cong (x ∷_) xs≡ys , res , ok

  bs-concat-[]⊎tf : ∀ as {bs} → true ∷ true ∷ bs ≢ bs-concat as
  bs-concat-[]⊎tf ([] ∷ as) ()
  bs-concat-[]⊎tf ((_ ∷ _) ∷ as) ()

  toBitString-pad'-≺
    : ∀{a b}
    → (a≺bbs : toBitString-pad' a ≺ toBitString-pad' b)
    → a ≡ b ⊎ ∃[ tail ] (≺-drop a≺bbs ≡ true ∷ true ∷ tail)
  toBitString-pad'-≺ {[]} {[]} prf     = inj₁ refl
  toBitString-pad'-≺ {[]} {x ∷ bs} z≺n = inj₂ (Vec-toList x ++ toBitString-pad' bs , refl)
  toBitString-pad'-≺ {a ∷ as} {b ∷ bs} (s≺s (s≺s prf))
    with ≺-respects-++-len (Vec-toList a) (Vec-toList b) prf
                           (trans (Vec-toList-length a) (sym (Vec-toList-length b)))
  ...| a≡b , prf' , drop≡
    with toBitString-pad'-≺ {as} {bs} prf'
  ...| inj₁ ok = inj₁ (cong₂ _∷_ (Vec-toList-inj a≡b) ok)
  ...| inj₂ ok = inj₂ (proj₁ ok , trans drop≡ (proj₂ ok))

  toBitString-pad-≺
    : ∀{a b}
    → (a≺bbs : toBitString-pad a ≺ toBitString-pad b)
    → a ≡ b ⊎ ∃[ tail ] (≺-drop a≺bbs ≡ true ∷ true ∷ tail)
  toBitString-pad-≺ {[]}    {[]} prf = inj₁ refl
  toBitString-pad-≺ {a ∷ as} {b ∷ bs} (s≺s (s≺s prf))
    with ≺-respects-++-len (Vec-toList a) (Vec-toList b) prf
                           (trans (Vec-toList-length a) (sym (Vec-toList-length b)))
  ...| a≡b , prf' , drop≡
    with toBitString-pad'-≺ {as} {bs} prf'
  ...| inj₁ ok = inj₁ (cong₂ _∷_ (Vec-toList-inj a≡b) ok)
  ...| inj₂ ok = inj₂ (proj₁ ok , trans drop≡ (proj₂ ok))

  bs-concat-inj : ∀ bs₁ bs₂ → bs-concat bs₁ ≡ bs-concat bs₂ → bs₁ ≡ bs₂
  bs-concat-inj [] [] hyp = refl
  bs-concat-inj ([] ∷ as) [] ()
  bs-concat-inj [] ([] ∷ bs) ()
  bs-concat-inj [] ((_ ∷ _) ∷ bs) ()
  bs-concat-inj ((_ ∷ _) ∷ as) [] ()
  bs-concat-inj (a ∷ as) (b ∷ bs) hyp -- TODO-1: Eliminate catchall warning or explain why we don't.
    with ++-≺ (toBitString-pad a) (toBitString-pad b) hyp
  ...| inj₁ (a≺b , prf)
    with toBitString-pad-≺ a≺b
  ...| inj₁ refl = cong (a ∷_) (bs-concat-inj as bs (proj₂ (++-len-injective (toBitString-pad a) _ refl hyp)))
  ...| inj₂ (tail , aux) rewrite aux = ⊥-elim (bs-concat-[]⊎tf as prf)
  bs-concat-inj (a ∷ as) (b ∷ bs) hyp
     | inj₂ (b≺a , prf)
    with toBitString-pad-≺ b≺a
  ...| inj₁ refl = cong (a ∷_) (bs-concat-inj as bs (proj₂ (++-len-injective (toBitString-pad a) _ refl hyp)))
  ...| inj₂ (tail , aux) rewrite aux  = ⊥-elim (bs-concat-[]⊎tf bs prf)
