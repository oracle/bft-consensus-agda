{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.PKCS

  -- This module provides a utility function to make it easy to provide the
  -- bft-lemma for implementations that assume one peer, one vote and assume
  -- that: at most bizF members are byzantine; authorsN ≥ suc (3 * bizF);
  -- and a list of Members is a quorum if it contains at least authorsN ∸
  -- bizF = QSize distinct Members. The bft-lemma is the last lemma in this
  -- file and proves that in the intersection of any two lists with at least
  -- QSize distinct Members there is an honest Member.

module LibraBFT.Abstract.BFT
  (authorsN  : ℕ)
  (bizF      : ℕ)
  (N         : ℕ)
  (votPower  : Fin authorsN → ℕ)
  (isBFT     : N ≥ suc (3 * bizF))
  (getPubKey : Fin authorsN → PK)


 where


 QSize : ℕ
 QSize = N ∸ bizF

 -- The set of members of this epoch.
 Member : Set
 Member = Fin authorsN

 Meta-dishonest? :  ∀ (m : Member) → Dec (Meta-Dishonest-PK (getPubKey m))
 Meta-dishonest? m = Meta-DishonestPK? (getPubKey m)

 CombinedPower : List Member → ℕ
 CombinedPower xs = sum (List-map votPower xs)

 --TODO-1 : replace IsSorted with allDistict
 module _  (votPowerT : N ≡ CombinedPower (List-tabulate id))
           (bft-assumption : ∀ {xs : List Member}
                           → IsSorted _<Fin_ xs
                           → CombinedPower (List-filter Meta-dishonest? xs) ≤ bizF)
   where

   _∈?_ : (x : Member) → (xs : List Member) → Dec (Any (x ≡_) xs)
   x ∈? xs = Any-any (x ≟Fin_) xs

   -- TODO-2 : Many of these lemmas can be generalized for any list or any
   -- IsSorted list of Fin. Perhaps establish a Lemmas.FinProps module.
   intersectElem : List Member → Member → List Member
   intersectElem [] y = []
   intersectElem (x ∷ xs) y
      with Fin-<-cmp x y
   ...| tri< a ¬b ¬c = intersectElem xs y
   ...| tri≈ ¬a b ¬c = y ∷ []
   ...| tri> ¬a ¬b c = []


   intersect : List Member → List Member → List Member
   intersect xs [] = []
   intersect xs (y ∷ ys) = intersectElem xs y ++ intersect xs ys


   unionElem : List Member → Member → List Member
   unionElem [] y = y ∷ []
   unionElem (x ∷ xs) y
     with Fin-<-cmp x y
   ...| tri< a ¬b ¬c = x ∷ unionElem xs y
   ...| tri≈ ¬a b ¬c = x ∷ xs
   ...| tri> ¬a ¬b c = y ∷ x ∷ xs


   union : List Member → List Member → List Member
   union xs [] = xs
   union xs (y ∷ ys) = unionElem (union xs ys) y


   intDiffElem : ∀ {slist} (xs : List Member)
               → (intS : IsSorted _<Fin_ slist)
               → (y : Member)
               → OnHead _<Fin_ y slist
               → IsSorted _<Fin_ (intersectElem xs y ++ slist)
   intDiffElem [] slist y x = slist
   intDiffElem (x ∷ xs) slist y yOH
     with Fin-<-cmp x y
   ...| tri< a ¬b ¬c = intDiffElem xs slist y yOH
   ...| tri≈ ¬a b ¬c = yOH ∷ slist
   ...| tri> ¬a ¬b c = slist


   trans-OnHead : ∀ {xs : List Member} {y x : Member}
                → OnHead _<Fin_ y xs
                → x <Fin y
                → OnHead _<Fin_ x xs
   trans-OnHead [] x<y = []
   trans-OnHead (on-∷ y<f) x<y = on-∷ (Fin-<-trans x<y y<f)


   ++-OnHead : ∀ {xs ys : List Member} {y : Member}
             → OnHead _<Fin_ y xs
             → OnHead _<Fin_ y ys
             → OnHead _<Fin_ y (xs ++ ys)
   ++-OnHead {[]} {ys} {y} xsOH ysOH = ysOH
   ++-OnHead {x ∷ xs} {ys} {y} (on-∷ y<x) ysOH = on-∷ y<x


   intElem-OnHead : ∀ {xs : List Member} {y x : Member}
                  → x <Fin y
                  → OnHead _<Fin_ x (intersectElem xs y)
   intElem-OnHead {[]} {y} {x} x<y = []
   intElem-OnHead {x₁ ∷ xs} {y} {x} x<y
      with Fin-<-cmp x₁ y
   ...| tri< a ¬b ¬c = intElem-OnHead {xs} x<y
   ...| tri≈ ¬a b ¬c = on-∷ x<y
   ...| tri> ¬a ¬b c = []


   int-OnHead : ∀ {xs ys : List Member} {y : Member}
              → IsSorted _<Fin_ (y ∷ ys)
              → OnHead _<Fin_ y (intersect xs ys)
   int-OnHead {xs} {[]} sl = []
   int-OnHead {xs} {y ∷ ys} (on-∷ p ∷ sl) = ++-OnHead (intElem-OnHead {xs} p)
                                                      (trans-OnHead (int-OnHead sl) p)


   intersectDiff : ∀ {xs ys : List Member}
                 → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                 → IsSorted _<Fin_ (intersect xs ys)
   intersectDiff {xs} {[]} _ _ = []
   intersectDiff {xs} {y ∷ ys} sxs (y₁ ∷ sys) = intDiffElem xs (intersectDiff sxs sys) y
                                                               (int-OnHead (y₁ ∷ sys))


   int-[]≡[] : (xs : List Member) → intersect [] xs ≡ []
   int-[]≡[] [] = refl
   int-[]≡[] (x ∷ xs) = int-[]≡[] xs


   ∈-intersectElem : ∀ {xs : List Member} {α y}
                     → α ∈ intersectElem xs y
                     → α ∈ xs × α ∈ y ∷ []
   ∈-intersectElem {x ∷ xs} {α} {y} ∈int
     with Fin-<-cmp x y
   ...| tri< a ¬b ¬c = (Any-++ʳ (x ∷ []) (proj₁ (∈-intersectElem ∈int))) , proj₂ (∈-intersectElem {xs} ∈int)
   ...| tri≈ ¬a refl ¬c = Any-++ˡ ∈int , ∈int
   ...| tri> ¬a ¬b c = contradiction ∈int ¬Any[]


   ∈-intersect : ∀ {xs ys : List Member} {α}
                 → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                 → α ∈ intersect xs ys → α ∈ xs × α ∈ ys
   ∈-intersect {[]} {y ∷ ys} sxs (y₁ ∷ sys) α∈∩ rewrite int-[]≡[] ys = contradiction α∈∩ ¬Any[]
   ∈-intersect {x ∷ xs} {y ∷ ys} sxs (y₁ ∷ sys) α∈∩
     with Fin-<-cmp x y
   ∈-intersect {x ∷ xs} {.x ∷ ys} sxs (y₁ ∷ sys) (here px) | tri≈ ¬a refl ¬c
     = here px , here px
   ∈-intersect {x ∷ xs} {.x ∷ ys} sxs (y₁ ∷ sys) (there α∈∩) | tri≈ ¬a refl ¬c
     = proj₁ (∈-intersect sxs sys α∈∩) , Any-++ʳ (x ∷ []) (proj₂ (∈-intersect sxs sys α∈∩))
   ...| tri> ¬a ¬b c
     = proj₁ (∈-intersect sxs sys α∈∩) , there (proj₂ (∈-intersect sxs sys α∈∩))
   ...| tri< a ¬b ¬c
     with Any-++⁻ (intersectElem xs y) α∈∩
   ...| inj₁ x₁ = Any-++ʳ (x ∷ []) (proj₁ (∈-intersectElem x₁)) , Any-++ˡ (proj₂ (∈-intersectElem {xs} x₁))
   ...| inj₂ y₂ = proj₁ (∈-intersect sxs sys y₂) , Any-++ʳ (y ∷ []) (proj₂ (∈-intersect sxs sys y₂))


   pred-Fin : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
   pred-Fin zero = zero
   pred-Fin (suc x) = x

   ∸-suc-≤ : ∀ (x w : ℕ) → suc x ∸ w ≤ suc (x ∸ w)
   ∸-suc-≤ x zero = ≤-refl
   ∸-suc-≤ zero (suc w) rewrite 0∸n≡0 w = z≤n
   ∸-suc-≤ (suc x) (suc w) = ∸-suc-≤ x w


   head-Sort : ∀ {n x l} {xs : List (Fin n)} → IsSorted _<Fin_ (x ∷ xs)
             → length (x ∷ xs) ≡ l → l ≤ n → toℕ x ≤ n ∸ l
   head-Sort {suc zero} {zero} {l} {xs} sxs eq l≤n = z≤n
   head-Sort {suc (suc n)} {x} {suc l} {x₁ ∷ xs} (on-∷ p ∷ sxs) eq l≤n
    with head-Sort sxs (cong pred eq) (≤pred⇒≤ (≤-pred l≤n))
   ...| rec = ≤-pred (≤-trans p (≤-trans rec (∸-suc-≤ (suc n) l)))
   head-Sort {suc (suc n)} {zero} {suc zero} {[]} (x₁ ∷ sxs) eq l≤n = z≤n
   head-Sort {suc (suc n)} {suc x} {suc zero} {[]} (x₁ ∷ sxs) eq l≤n
     = s≤s (head-Sort ([] ∷ []) eq (s≤s z≤n))


   sorted-length : ∀ {n} {xs : List (Fin n)} → IsSorted _<Fin_ xs
                 → length xs ≤ n
   sorted-length {n} {[]} x = z≤n
   sorted-length {suc n} {x₁ ∷ []} (x ∷ sxs) = s≤s z≤n
   sorted-length {suc n} {x₁ ∷ x₂ ∷ xs} (x ∷ sxs)
     with m≤n⇒m<n∨m≡n (sorted-length sxs)
   ...| inj₁ l<n = l<n
   ...| inj₂ l≡n
     with head-Sort sxs l≡n ≤-refl
   ...| xxx
     with subst (toℕ x₂ ≤_) (n∸n≡0 n) xxx
   sorted-length {suc n} {x₁ ∷ zero ∷ xs} (on-∷ () ∷ sxs) | inj₂ y | xxx | yy


   union-sorted :  ∀ {xs ys : List Member}
                → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                → IsSorted _<Fin_ (union xs ys)
   union-sorted {xs} {[]} sxs sys = sxs
   union-sorted {xs} {y ∷ ys} sxs (y₁ ∷ sys) = unionElem-sorted (union-sorted sxs sys)
     where union-OnHead : ∀ {xs : List Member} {x y}
                        → IsSorted _<Fin_ (x ∷ xs)
                        → x <Fin y
                        → OnHead _<Fin_ x (unionElem xs y)
           union-OnHead {[]} {x} {y} sxs x<y = on-∷ x<y
           union-OnHead {x₁ ∷ xs} {x} {y} (on-∷ xx ∷ sxs) x<y
              with Fin-<-cmp x₁ y
           ...| tri< a ¬b ¬c = on-∷ xx
           ...| tri≈ ¬a b ¬c = on-∷ xx
           ...| tri> ¬a ¬b c = on-∷ x<y

           unionElem-sorted : ∀ {xs y} → IsSorted _<Fin_ xs
                            → IsSorted _<Fin_ (unionElem xs y)
           unionElem-sorted {[]} {y} [] = [] ∷ []
           unionElem-sorted {(x ∷ xs)} {y} (x₁ ∷ sxs)
             with Fin-<-cmp x y
           ...| tri< a ¬b ¬c = union-OnHead (x₁ ∷ sxs) a ∷ (unionElem-sorted sxs)
           ...| tri≈ ¬a b ¬c = (x₁ ∷ sxs)
           ...| tri> ¬a ¬b c = on-∷ c ∷ (x₁ ∷ sxs)


   union-length-UpLim : ∀ {xs ys : List Member}
                      → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                      → length (union xs ys) ≤ authorsN
   union-length-UpLim sxs sys = sorted-length (union-sorted sxs sys)



   xxx : ∀ {n} {xs : List (Fin n)} {f : Fin n → ℕ}
       → IsSorted _<Fin_ xs
       → length xs ≤ n
       → sum (List-map f xs) ≤ sum (List-map f (List-tabulate id))
   xxx {n} {[]} {f} sxs l≤n = {!!}
   xxx {suc n} {x ∷ xs} {f} sxs l≤n = {!!}



   votingPower≤N : ∀ {xs : List Member} → IsSorted _<Fin_ xs
                   → CombinedPower xs ≤ N
   votingPower≤N {[]} sxs = z≤n
   votingPower≤N {zero ∷ xs} (x₁ ∷ sxs) rewrite votPowerT = {!!}
   votingPower≤N {suc x ∷ xs} (x₁ ∷ sxs) = {!!}


   union-votPower : ∀ {xs ys : List Member}
                      → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                      → CombinedPower (union xs ys) ≤ N
   union-votPower {xs} {ys} sxs sys = votingPower≤N (union-sorted sxs sys)
   --  with union-sorted sxs sys
   --...| sorted|q₁∪q₂| rewrite votPowerT
   --  = xxx sorted|q₁∪q₂| (sorted-length sorted|q₁∪q₂|)


   union-∈ : ∀ {xs} {x} (ys : List Member)
           → x ∈ xs → x ∈ union xs ys
   union-∈ {xs} {x} [] x∈xs = x∈xs
   union-∈ {xs} {x} (y ∷ ys) x∈xs = unionElem-∈ (union-∈ ys x∈xs)
     where unionElem-∈ : ∀ {xs : List Member} {x y} → x ∈ xs
                         → x ∈ unionElem xs y
           unionElem-∈ {x₁ ∷ xs} {x} {y} (here px)
             with Fin-<-cmp x₁ y
           ...| tri< a ¬b ¬c = here px
           ...| tri≈ ¬a b ¬c = here px
           ...| tri> ¬a ¬b c = there (here px)
           unionElem-∈ {x₁ ∷ xs} {x} {y} (there x∈xs)
             with Fin-<-cmp x₁ y
           ...| tri< a ¬b ¬c = there (unionElem-∈ x∈xs)
           ...| tri≈ ¬a b ¬c = there x∈xs
           ...| tri> ¬a ¬b c = there (there x∈xs)


   unionElem-∈-disj : ∀ {y x} (xs : List Member) → y ∈ unionElem xs x
                    → y ≡ x ⊎ y ∈ xs
   unionElem-∈-disj {y} {x} [] (here px) = inj₁ px
   unionElem-∈-disj {y} {x} (x₁ ∷ xs) y∈
     with Fin-<-cmp x₁ x
   ...| tri≈ ¬a b ¬c = inj₂ y∈
   unionElem-∈-disj {y} {x} (x₁ ∷ xs) (here px) | tri> ¬a ¬b c = inj₁ px
   unionElem-∈-disj {y} {x} (x₁ ∷ xs) (there y∈) | tri> ¬a ¬b c = inj₂ y∈
   unionElem-∈-disj {y} {x} (x₁ ∷ xs) (here px) | tri< a ¬b ¬c = inj₂ (here px)
   unionElem-∈-disj {y} {x} (x₁ ∷ xs) (there y∈) | tri< a ¬b ¬c
     with unionElem-∈-disj xs y∈
   ...| inj₁ y≡x  = inj₁ y≡x
   ...| inj₂ y∈xs = inj₂ (there y∈xs)


   union-∈-disj : ∀ {y} (xs ys : List Member) → y ∈ union xs ys
                → y ∈ xs ⊎ y ∈ ys
   union-∈-disj xs [] y∈ = inj₁ y∈
   union-∈-disj xs (x ∷ ys) y∈
     with unionElem-∈-disj (union xs ys) y∈
   ...| inj₁ y≡x = inj₂ (here y≡x)
   ...| inj₂ y∈un
     with union-∈-disj xs ys y∈un
   ...| inj₁ y∈xs = inj₁ y∈xs
   ...| inj₂ y∈ys = inj₂ (there y∈ys)


   union-∉ : ∀ {ys xs : List Member} {y}
           → y ∉ ys → y ∉ xs → y ∉ union xs ys
   union-∉ {ys} {xs} {y} y∉ys y∉xs y∈union
     with union-∈-disj xs ys y∈union
   ...| inj₁ y∈xs = ⊥-elim (y∉xs y∈xs)
   ...| inj₂ y∈ys = ⊥-elim (y∉ys y∈ys)


   unionElemLength-∈ : ∀ {xs : List Member} {x} → x ∈ xs → IsSorted _<Fin_ xs
                     → length (unionElem xs x) ≡ length xs
   unionElemLength-∈ {x ∷ xs} (here refl) _
     with Fin-<-cmp x x
   ...| tri< a ¬b ¬c = ⊥-elim (¬b refl)
   ...| tri≈ ¬a b ¬c = refl
   ...| tri> ¬a ¬b c = ⊥-elim (¬b refl)
   unionElemLength-∈ {x ∷ xs} {x₁} (there x∈) (x₂ ∷ sxs)
     with Fin-<-cmp x x₁
   ...| tri< a ¬b ¬c = cong suc (unionElemLength-∈ x∈ sxs)
   ...| tri≈ ¬a b ¬c = refl
   ...| tri> ¬a ¬b c = ⊥-elim (<⇒≱ c (≤-head (there x∈) (x₂ ∷ sxs)))
     where  ≤-head : ∀ {xs : List Member} {x y}
                   → y ∈ (x ∷ xs) → IsSorted _<Fin_ (x ∷ xs)
                   → x ≤Fin y
            ≤-head {xs} {x} {x} (here refl) sxs = ≤-refl
            ≤-head {x₁ ∷ []} {x} {x₁} (there (here refl)) (on-∷ x< ∷ sxs) = <⇒≤ x<
            ≤-head {x₁ ∷ x₂ ∷ xs} {x} {y} (there y∈) (on-∷ x<x₁ ∷ sxs)
              = ≤-trans (<⇒≤ x<x₁) (≤-head y∈ sxs)


   y∉⇒All≢ : ∀ {xs : List Member} {x y} → y ∉ (x ∷ xs)
           → x ≢ y × y ∉ xs
   y∉⇒All≢ {xs} {x} {y} y∉
     with y ∈? xs
   ...| yes y∈xs = ⊥-elim (y∉ (there y∈xs))
   ...| no  y∉xs
     with x ≟Fin y
   ...| yes x≡y = ⊥-elim (y∉ (here (sym x≡y)))
   ...| no  x≢y = x≢y , y∉xs


   unionElem-∉ : ∀ {xs : List Member} {y} → y ∉ xs
               → length (unionElem xs y) ≡ 1 + length xs
   unionElem-∉ {[]} {y} _ = refl
   unionElem-∉ {x ∷ xs} {y} x∉
     with Fin-<-cmp x y
   ...| tri< a ¬b ¬c = cong suc (unionElem-∉ (proj₂ (y∉⇒All≢ x∉)))
   ...| tri≈ ¬a b ¬c = contradiction b (proj₁ (y∉⇒All≢ x∉))
   ...| tri> ¬a ¬b c = refl


   h∉t : ∀ {xs : List Member} {x} → IsSorted _<Fin_ (x ∷ xs) → x ∉ xs
   h∉t {x₁ ∷ xs} {x} (on-∷ x< ∷ sxs) (here refl) = ⊥-elim (<⇒≢ x< refl)
   h∉t {x₁ ∷ xs} {x} (on-∷ x< ∷ (x₁< ∷ sxs)) (there x∈xs) = h∉t ((trans-OnHead x₁< x<) ∷ sxs) x∈xs


   intersectElem-∈ : ∀ {xs : List Member} {x} → x ∈ xs → IsSorted _<Fin_ xs
                   → length (intersectElem xs x) ≡ 1
   intersectElem-∈ {x₁ ∷ xs} {x₁} (here refl) _
     with Fin-<-cmp x₁ x₁
   ...| tri< a ¬b ¬c = ⊥-elim (¬b refl)
   ...| tri≈ ¬a b ¬c = refl
   ...| tri> ¬a ¬b c = ⊥-elim (¬b refl)
   intersectElem-∈ {x₁ ∷ xs} {x} (there x∈xs) (xx ∷ sxs)
        with Fin-<-cmp x₁ x
   ...| tri< a ¬b ¬c = intersectElem-∈ x∈xs sxs
   ...| tri≈ ¬a b ¬c = refl
   ...| tri> ¬a ¬b c = contradiction (there x∈xs) (h∉t (on-∷ c ∷ xx ∷ sxs))


   intersectElem-∉ : ∀ {xs : List Member} {x} → x ∉ xs
                   → length (intersectElem xs x) ≡ 0
   intersectElem-∉ {[]} {x} x∉xs = refl
   intersectElem-∉ {x₁ ∷ xs} {x} x∉xs
     with Fin-<-cmp x₁ x
   ...| tri< a ¬b ¬c = intersectElem-∉ (proj₂ (y∉⇒All≢ x∉xs))
   ...| tri≈ ¬a b ¬c = ⊥-elim (proj₁ (y∉⇒All≢ x∉xs) b)
   ...| tri> ¬a ¬b c = refl


   length-int-≤ : ∀ (xs ys : List Member) → IsSorted _<Fin_ xs
                → length (intersect xs ys) ≤ length ys
   length-int-≤ xs [] _ = z≤n
   length-int-≤ xs (y ∷ ys) sxs
     with y ∈? xs
   ...| yes y∈xs rewrite length-++ (intersectElem xs y) {intersect xs ys}
                        | intersectElem-∈ y∈xs sxs = s≤s (length-int-≤ xs ys sxs)
   ...| no  y∉xs rewrite length-++ (intersectElem xs y) {intersect xs ys}
                        | intersectElem-∉ y∉xs = ≤-step (length-int-≤ xs ys sxs)


   union-length≡ : ∀ {xs ys : List Member}
                 → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                 → length (union xs ys) ≡ length xs + length ys ∸ length (intersect xs ys)
   union-length≡ {xs} {[]} sxs sys rewrite +-identityʳ (length xs) = refl
   union-length≡ {xs} {y ∷ ys} sxs (y₁ ∷ sys)
     rewrite length-++ (intersectElem xs y) {intersect xs ys}
     with y ∈? xs
   ...| yes y∈xs rewrite unionElemLength-∈ (union-∈ ys y∈xs) (union-sorted sxs sys)
                        | intersectElem-∈ y∈xs sxs
                        | +-∸-assoc (length xs) (s≤s (length-int-≤ xs ys sxs))
                        | sym (+-∸-assoc (length xs) (length-int-≤ xs ys sxs))
                        = union-length≡ sxs sys
   ...| no  y∉xs rewrite unionElem-∉ (union-∉ (h∉t (y₁ ∷ sys)) y∉xs)
                        | intersectElem-∉ y∉xs
                        | +-suc (length xs) (length ys)
                        | +-∸-assoc 1 (≤-stepsˡ (length xs) (length-int-≤ xs ys sxs))
                        = cong suc (union-length≡ sxs sys)


   unionElem-∈-≡ : ∀ {xs : List Member} {x}
                 → x ∈ xs → IsSorted _<Fin_ xs
                 → unionElem xs x ≡ xs


   intersectElem-∈-≡ : ∀ {xs : List Member} {x}
                     → x ∈ xs → IsSorted _<Fin_ xs
                     → intersectElem xs x ≡ x ∷ []

   intersectElem-∉-[] :  ∀ {xs : List Member} {x} → x ∉ xs → IsSorted _<Fin_ xs
                         → intersectElem xs x ≡ []


   unionElem-∉-sum : ∀ {xs : List Member} {x} (f : Member → ℕ) → x ∉ xs
                   → sum (List-map f (unionElem xs x)) ≡ f x + sum (List-map f xs)

   sumIntersect≤ : ∀ {xs ys : List Member} (f : Member → ℕ)
                 → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                 → sum (List-map f (intersect xs ys)) ≤ sum (List-map f (xs ++ ys))


   union-votPower≡ :  ∀ {xs ys : List Member}
                      → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                      → CombinedPower (union xs ys) ≡ CombinedPower (xs ++ ys) ∸ CombinedPower (intersect xs ys)
   union-votPower≡ {xs} {[]} sxs sys
     rewrite map-++-commute votPower xs []
           | sum-++-commute (List-map votPower xs) []
           | +-identityʳ (CombinedPower xs) = refl
   union-votPower≡ {xs} {y ∷ ys} sxs (y₁ ∷ sys)
      with y ∈? xs
   ...| yes y∈xs rewrite unionElem-∈-≡ (union-∈ ys y∈xs) (union-sorted sxs sys)
                       | union-votPower≡ sxs sys
                       | sym (m+n∸n≡m (CombinedPower (xs ++ ys)) (votPower y))
                       | ∸-+-assoc (CombinedPower (xs ++ ys) + votPower y)
                                   (votPower y)
                                   (CombinedPower (intersect xs ys))
                       | map-++-commute votPower xs ys
                       | sum-++-commute (List-map votPower xs) (List-map votPower ys)
                       | +-assoc (CombinedPower xs)
                                 (CombinedPower ys)
                                 (votPower y)
                       | +-comm (CombinedPower ys) (votPower y)
                       | map-++-commute votPower xs (y ∷ ys)
                       | sum-++-commute (List-map votPower xs) (List-map votPower (y ∷ ys))
                       | map-++-commute votPower (intersectElem xs y) (intersect xs ys)
                       | sum-++-commute (List-map votPower (intersectElem xs y))
                                        (List-map votPower (intersect xs ys))
                       | intersectElem-∈-≡ y∈xs sxs
                       | +-identityʳ (votPower y) = refl

   ...| no  y∉xs rewrite map-++-commute votPower xs (y ∷ ys)
                       | sum-++-commute (List-map votPower xs) (List-map votPower (y ∷ ys))
                       | sym (+-assoc (CombinedPower xs)
                                      (votPower y)
                                      (CombinedPower ys))
                       | +-comm (CombinedPower xs) (votPower y)
                       | unionElem-∉-sum votPower (union-∉ (h∉t (y₁ ∷ sys)) y∉xs)
                       | union-votPower≡ sxs sys
                       | intersectElem-∉-[] y∉xs sxs
                       | +-assoc (votPower y)
                                 (CombinedPower xs)
                                 (CombinedPower ys)
                       | sym (sum-++-commute (List-map votPower xs) (List-map votPower ys))
                       | sym (map-++-commute votPower xs ys)
                       | +-∸-assoc (votPower y) (sumIntersect≤ votPower sxs sys) = refl


   m∸n≤o⇒m∸o≤n : ∀ (x z w : ℕ) → x ∸ z ≤ w → x ∸ w ≤ z
   m∸n≤o⇒m∸o≤n x zero w p≤ rewrite m≤n⇒m∸n≡0 p≤ = z≤n
   m∸n≤o⇒m∸o≤n zero (suc z) w p≤ rewrite 0∸n≡0 w = z≤n
   m∸n≤o⇒m∸o≤n (suc x) (suc z) w p≤ = ≤-trans (∸-suc-≤ x w) (s≤s (m∸n≤o⇒m∸o≤n x z w p≤))


   quorumInt>biz : ∀ (xs ys : List Member)
                 → QSize ≤ CombinedPower xs
                 → QSize ≤ CombinedPower ys
                 → CombinedPower (xs ++ ys) ∸ N ≤ CombinedPower (intersect xs ys)
                 → bizF + 1 ≤ CombinedPower (intersect xs ys)
   quorumInt>biz xs ys q≤x q≤y ≤int = {!!}
   {-  let p₁ = ≤-trans (∸-monoˡ-≤ authorsN (+-mono-≤ q≤x q≤y)) ≤int
         p₂ = subst (_≤ length (intersect xs ys)) (simpExp₁ authorsN bizF) p₁
         p₃ = ≤-trans (∸-monoˡ-≤ (2 * bizF) isBFT) p₂
     in subst (_≤ length (intersect xs ys)) (simpExp₂ bizF) p₃
       where  simpExp₁ : ∀ (x y : ℕ) → (x ∸ y) + (x ∸ y) ∸ x ≡ x ∸ (2 * y)
              simpExp₁ x y rewrite sym (*-identityʳ (x ∸ y))
                                 | sym (*-distribˡ-+ (x ∸ y) 1 1)
                                 | *-comm (x ∸ y) 2
                                 | *-distribˡ-∸ 2 x y
                                 | ∸-+-assoc (2 * x) (2 * y) x
                                 | +-comm (2 * y) x
                                 | sym (∸-+-assoc (2 * x) x (2 * y))
                                 | +-identityʳ x
                                 | m+n∸n≡m x x = refl

              simpExp₂ : ∀ (x : ℕ) → suc (3 * x) ∸ 2 * x ≡ x + 1
              simpExp₂ x rewrite +-∸-assoc 1 (*-monoˡ-≤ x {2} {3} (s≤s (s≤s z≤n)))
                               | sym (*-distribʳ-∸ x 3 2)
                               | sym (+-suc x 0) = refl -}


   span-hon : ∀ {xs dis hon : List Member} {x : Member}
            → span Meta-dishonest? xs ≡ (dis , x ∷ hon)
            → x ∈ xs ×  Meta-Honest-PK (getPubKey x)
   span-hon {x ∷ xs} {dis} {hon} eq
     with Meta-dishonest? x | eq
   ...| no imp  | refl = here refl , imp
   ...| yes prf | eq₁
     with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| fst , x₂ ∷ snd | [ eq₂ ] rewrite just-injective (cong (head ∘ proj₂) eq₁)
     = ×-map₁ there (span-hon eq₂)


   span-dis : ∀ {xs dis : List Member}
            → span Meta-dishonest? xs ≡ (dis , [])
            → length xs ≡ length (List-filter Meta-dishonest? xs)
   span-dis {[]} {dis} eq = refl
   span-dis {x ∷ xs} {dis} eq
     with Meta-dishonest? x | eq
   ...| no ¬dis  | ()
   ...| yes prf  | _
     with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| fst , [] | [ eq₁ ] = cong suc (span-dis {xs} eq₁)


   -- TODO-1 : An alternative to prove this lemma would be:
   -- - First use the library lemma length-filter to prove that
   --   length (List-filter Meta-dishonest? xs) ≤ length xs.
   -- - Then prove that if length (List-filter Meta-dishonest? xs) < length xs
   --   then ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α)).
   -- - Otherwise, if length (List-filter Meta-dishonest? xs ≡ )length xs we
   --   get a contradiction using the bft assumption (as we have now).
   find-honest : ∀ {xs : List Member}
               → IsSorted _<Fin_ xs
               → bizF + 1 ≤ CombinedPower xs
               → ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α))
   find-honest {xs} sxs biz< = {!!}
   {-  with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| dis , [] | [ eq ] rewrite +-comm bizF 1
                                 | span-dis {xs} eq = ⊥-elim (<⇒≱ biz< {!!}) --(bft-assumption sxs))
   ...| dis , x ∷ hon | [ eq ] = x , (span-hon eq) -}


   bft-lemma : {xs ys : List Member}
             -- enforcing both xs and ys to be sorted lists according to
             -- a anti-reflexive linear order ensures authors are distinct.
             → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
             → QSize ≤ CombinedPower xs
             → QSize ≤ CombinedPower ys
             → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-PK (getPubKey α))
   bft-lemma {xs} {ys} difxs difys q≤xs q≤ys
     = let |q₁|+|q₂|   = CombinedPower (xs ++ ys)
           |q₁∩q₂|     = CombinedPower (intersect xs ys)
           |q₁∪q₂|≤n   = union-votPower difxs difys
           exp₁        = subst (_≤ N) (union-votPower≡ difxs difys) |q₁∪q₂|≤n
           exp₂        = m∸n≤o⇒m∸o≤n |q₁|+|q₂| |q₁∩q₂| N exp₁
           f+1≤|q₁∩q₂| = quorumInt>biz xs ys q≤xs q≤ys exp₂
           honInf      = find-honest (intersectDiff difxs difys) f+1≤|q₁∩q₂|
           h∈∩         = ∈-intersect difxs difys ((proj₁ ∘ proj₂) honInf)
       in proj₁ honInf , proj₁ h∈∩ , proj₂ h∈∩ , (proj₂ ∘ proj₂) honInf



