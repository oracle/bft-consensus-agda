{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.PKCS

  -- This module provides a utility function to make it easy to
  -- provide the bft-lemma for implementations in which the
  -- participants can hve different voting power.

  -- The module should be parametrized with the number of participants
  -- - `authorsN`, and with a function - `votPower` - that assigns to
  -- each participant its voting power. The parameter `N` corresponds
  -- to the total voting power of all participants, as required by the
  -- parameter `totalVotPower` in the inner module. These
  -- implementations should assume a fixed unknown subset of malicious
  -- nodes - Byzantine - but should also assume a security threshold
  -- `bizF`, such that N > 3 * bizF, which should be provided in
  -- parameter `isBFT`.  Finally, the `bft-assumption` states that the
  -- combined voting power of Byzantine nodes must not exceed the
  -- security threshold `bizF`. A quorum is a subset of distinct nodes
  -- whose combined voting power `QSize` satisfies `QSize ≥ N ∸ bizF`,
  -- received as the parameter `quorumVotPower` in the ineer module.

  -- The bft-lemma is the last lemma in this file and proves that in
  -- the intersection of any quoruns there is an honest Member.

module LibraBFT.Abstract.BFT
  (authorsN  : ℕ)
  (votPower  : Fin authorsN → ℕ)
  (N         : ℕ)
  (bizF      : ℕ)
  (isBFT     : N ≥ suc (3 * bizF))
  (QSize     : ℕ)
  (getPubKey : Fin authorsN → PK)


 where


 -- The set of members of this epoch.
 Member : Set
 Member = Fin authorsN

 Meta-dishonest? :  ∀ (m : Member) → Dec (Meta-Dishonest-PK (getPubKey m))
 Meta-dishonest? m = Meta-DishonestPK? (getPubKey m)

 CombinedPower : List Member → ℕ
 CombinedPower xs = sum (List-map votPower xs)

 -- The bft-assumption states that the combined voting power of
 -- Byzantine nodes must not exceed the security threshold
 -- `bizF`. Therefore, for any possible list of distinct participants
 -- the combined power of the dishonest nodes is less or equal than
 -- `bizF`. To express a list of distinct particpants we used the data
 -- type `IsSorted _<Fin_`, enforcing xs to be sorted according to a
 -- anti-reflexive linear order ensures authors are distinct.
 -- TODO-1 : Replace `IsSorted _<Fin_ xs` with the type `allDistinct` in
 -- `LibraBFT.Lemmas
 module _  (totalVotPower  : N ≡ CombinedPower (List-tabulate id))
           (quorumVotPower : QSize ≥ N ∸ bizF)
           (bft-assumption : ∀ {xs : List Member}
                           → IsSorted _<Fin_ xs
                           → CombinedPower (List-filter Meta-dishonest? xs) ≤ bizF)
   where

   _∈?_ : ∀ {n} (x : Fin n) → (xs : List (Fin n)) → Dec (Any (x ≡_) xs)
   x ∈? xs = Any-any (x ≟Fin_) xs

   participants : List Member
   participants = List-tabulate id

   -- TODO-2 : Many of these lemmas can be generalized for any list or any
   -- IsSorted list of Fin. Perhaps establish a Lemmas.FinProps module.


   -- The `intersect` and `union` functions assume that the lists are
   -- sorted
   intersectElem : List Member → Member → List Member
   intersectElem [] y = []
   intersectElem (x ∷ xs) y
      with Fin-<-cmp x y
   ...| tri< _ _ _ = intersectElem xs y
   ...| tri≈ _ _ _ = y ∷ []
   ...| tri> _ _ _ = []


   intersect : List Member → List Member → List Member
   intersect xs [] = []
   intersect xs (y ∷ ys) = intersectElem xs y ++ intersect xs ys


   unionElem : List Member → Member → List Member
   unionElem [] y = y ∷ []
   unionElem (x ∷ xs) y
     with Fin-<-cmp x y
   ...| tri< _ _ _ = x ∷ unionElem xs y
   ...| tri≈ _ _ _ = x ∷ xs
   ...| tri> _ _ _ = y ∷ x ∷ xs


   union : List Member → List Member → List Member
   union xs [] = xs
   union xs (y ∷ ys) = unionElem (union xs ys) y


   ≤-head : ∀ {n} {xs : List (Fin n)} {x y}
          → y ∈ (x ∷ xs) → IsSorted _<Fin_ (x ∷ xs)
          → x ≤Fin y
   ≤-head (here refl) _ = ≤-refl
   ≤-head (there y∈) (on-∷ x<x₁ ∷ sxs)
     = ≤-trans (<⇒≤ x<x₁) (≤-head y∈ sxs)


   y∉⇒All≢ : ∀ {n} {xs : List (Fin n)} {x y}
           → y ∉ (x ∷ xs)
           → x ≢ y × y ∉ xs
   y∉⇒All≢ {_} {xs} {x} {y} y∉
     with y ∈? xs
   ...| yes y∈xs = ⊥-elim (y∉ (there y∈xs))
   ...| no  y∉xs
     with x ≟Fin y
   ...| yes x≡y = ⊥-elim (y∉ (here (sym x≡y)))
   ...| no  x≢y = x≢y , y∉xs


   intersectElem-∈-≡ : ∀ {xs : List Member} {x}
                     → x ∈ xs → IsSorted _<Fin_ xs
                     → intersectElem xs x ≡ x ∷ []
   intersectElem-∈-≡ {x₁ ∷ xs} {.x₁} (here refl) sxs
     with Fin-<-cmp x₁ x₁
   ...| tri< _ ¬b _ = ⊥-elim (¬b refl)
   ...| tri≈ _ _ _ = refl
   ...| tri> _ ¬b _ = ⊥-elim (¬b refl)
   intersectElem-∈-≡ {x₁ ∷ xs} {x} (there x∈xs) (x₂ ∷ sxs)
     with Fin-<-cmp x₁ x
   ...| tri< a ¬b ¬c = intersectElem-∈-≡ x∈xs sxs
   ...| tri≈ ¬a b ¬c = refl
   ...| tri> ¬a ¬b c = ⊥-elim (<⇒≱ c (≤-head (there x∈xs) (x₂ ∷ sxs)))


   intersectElem-∉-[] : ∀ {xs : List Member} {x}
                      → x ∉ xs
                      → intersectElem xs x ≡ []
   intersectElem-∉-[] {[]}      {x} x∉xs = refl
   intersectElem-∉-[] {x₁ ∷ xs} {x} x∉xs
      with Fin-<-cmp x₁ x
   ...| tri< _ _ _ = intersectElem-∉-[] (proj₂ (y∉⇒All≢ x∉xs))
   ...| tri≈ _ b _ = ⊥-elim (proj₁ (y∉⇒All≢ x∉xs) b)
   ...| tri> _ _ _ = refl


   trans-OnHead : ∀ {n} {xs : List (Fin n)} {y x : Fin n}
                → OnHead _<Fin_ y xs
                → x <Fin y
                → OnHead _<Fin_ x xs
   trans-OnHead [] _ = []
   trans-OnHead (on-∷ y<f) x<y = on-∷ (Fin-<-trans x<y y<f)


   ++-OnHead : ∀ {xs ys : List Member} {y : Member}
             → OnHead _<Fin_ y xs
             → OnHead _<Fin_ y ys
             → OnHead _<Fin_ y (xs ++ ys)
   ++-OnHead []         y<y₁ = y<y₁
   ++-OnHead (on-∷ y<x) _    = on-∷ y<x


   intElem-OnHead : ∀ {xs : List Member} {y x : Member}
                  → x <Fin y
                  → OnHead _<Fin_ x (intersectElem xs y)
   intElem-OnHead {[]} _ = []
   intElem-OnHead {x₁ ∷ xs} {y} x<y
      with Fin-<-cmp x₁ y
   ...| tri< _ _ _ = intElem-OnHead {xs} x<y
   ...| tri≈ _ _ _ = on-∷ x<y
   ...| tri> _ _ _ = []


   int-OnHead : ∀ {xs ys : List Member} {y : Member}
              → IsSorted _<Fin_ (y ∷ ys)
              → OnHead _<Fin_ y (intersect xs ys)
   int-OnHead      ([] ∷ _) = []
   int-OnHead {xs} (on-∷ p ∷ sxs) = ++-OnHead (intElem-OnHead {xs} p)
                                              (trans-OnHead (int-OnHead sxs) p)


   int-[]≡[] : (xs : List Member) → intersect [] xs ≡ []
   int-[]≡[] [] = refl
   int-[]≡[] (x ∷ xs) = int-[]≡[] xs


   intersectDiff : ∀ {xs ys : List Member}
                 → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                 → IsSorted _<Fin_ (intersect xs ys)
   intersectDiff {_}  {.[]}   _   [] = []
   intersectDiff {xs} {y ∷ _} sxs (y< ∷ sys)
     with y ∈? xs
   ...| yes y∈xs rewrite intersectElem-∈-≡ y∈xs sxs
        = int-OnHead (y< ∷ sys) ∷ intersectDiff sxs sys
   ...| no  y∉xs rewrite intersectElem-∉-[] y∉xs = intersectDiff sxs sys


   ∈-intersectElem : ∀ {α y} (xs : List Member)
                   → α ∈ intersectElem xs y
                   → α ∈ xs × α ∈ y ∷ []
   ∈-intersectElem {_} {y} (x ∷ xs) ∈int
     with Fin-<-cmp x y
   ...| tri< _ _ _
        = Any-++ʳ (x ∷ []) (proj₁ (∈-intersectElem xs ∈int)) , proj₂ (∈-intersectElem xs ∈int)
   ...| tri≈ _ refl _ = Any-++ˡ ∈int , ∈int
   ...| tri> _ _ _    = contradiction ∈int ¬Any[]


   ∈-intersect : ∀ {xs ys : List Member} {α}
               → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
               → α ∈ intersect xs ys
               → α ∈ xs × α ∈ ys
   ∈-intersect {[]} {_ ∷ ys} [] (_ ∷ _) α∈∩ rewrite int-[]≡[] ys
     = contradiction α∈∩ ¬Any[]
   ∈-intersect {x ∷ xs} {y ∷ _} sxs (_ ∷ sys) α∈∩
     with Fin-<-cmp x y  | α∈∩
   ...| tri≈ _ refl _    | here refl
        = here refl , here refl
   ...| tri≈ _ refl _    | there α∈
        = proj₁ (∈-intersect sxs sys α∈) , Any-++ʳ (x ∷ []) (proj₂ (∈-intersect sxs sys α∈))
   ...| tri> _ _ _       | α∈
        = proj₁ (∈-intersect sxs sys α∈) , there (proj₂ (∈-intersect sxs sys α∈))
   ...| tri< _ _ _       | α∈
     with Any-++⁻ (intersectElem xs y) α∈
   ...| inj₁ x₁ = Any-++ʳ (x ∷ []) (proj₁ (∈-intersectElem xs x₁))
                , Any-++ˡ (proj₂ (∈-intersectElem xs x₁))
   ...| inj₂ y₂ = proj₁ (∈-intersect sxs sys y₂)
                , Any-++ʳ (y ∷ []) (proj₂ (∈-intersect sxs sys y₂))


   unionSorted :  ∀ {xs ys : List Member}
                → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                → IsSorted _<Fin_ (union xs ys)
   unionSorted sxs [] = sxs
   unionSorted sxs (y₁ ∷ sys) = unionElem-sorted (unionSorted sxs sys)
     where union-OnHead : ∀ {xs : List Member} {x y}
                        → IsSorted _<Fin_ (x ∷ xs)
                        → x <Fin y
                        → OnHead _<Fin_ x (unionElem xs y)
           union-OnHead {[]} {_} {_} _ x<y = on-∷ x<y
           union-OnHead {x₁ ∷ _} {x} {y} (on-∷ x<x₁ ∷ _) x<y
              with Fin-<-cmp x₁ y
           ...| tri< _ _ _ = on-∷ x<x₁
           ...| tri≈ _ _ _ = on-∷ x<x₁
           ...| tri> _ _ _ = on-∷ x<y

           unionElem-sorted : ∀ {xs y} → IsSorted _<Fin_ xs
                            → IsSorted _<Fin_ (unionElem xs y)
           unionElem-sorted {[]} {y} [] = [] ∷ []
           unionElem-sorted {x ∷ xs} {y} (x< ∷ sxs)
             with Fin-<-cmp x y
           ...| tri< a _ _ = union-OnHead (x< ∷ sxs) a ∷ (unionElem-sorted sxs)
           ...| tri≈ _ _ _ = (x< ∷ sxs)
           ...| tri> _ _ c = on-∷ c ∷ (x< ∷ sxs)


   h∉t : ∀ {n} {xs : List (Fin n)} {x}
       → IsSorted _<Fin_ (x ∷ xs)
       → x ∉ xs
   h∉t (on-∷ x< ∷ sxs) (here refl) = ⊥-elim (<⇒≢ x< refl)
   h∉t (on-∷ x< ∷ (x₁< ∷ sxs)) (there x∈xs)
     = h∉t ((trans-OnHead x₁< x<) ∷ sxs) x∈xs


   _⊆List_ : ∀ {A : Set} → List A → List A → Set
   xs ⊆List ys = All (_∈ ys) xs


   ∈List-elim : ∀ {A : Set} {x y : A} {ys : List A}
              → x ∈ (y ∷ ys) → x ≢ y
              → x ∈ ys
   ∈List-elim (here x≡y) x≢y = ⊥-elim (x≢y x≡y)
   ∈List-elim (there x∈) x≢y = x∈


   ⊆List-elim : ∀ {n} {y} {xs ys : List (Fin n)}
              → xs ⊆List (y ∷ ys) → y ∉ xs
              → xs ⊆List ys
   ⊆List-elim [] y∉ = []
   ⊆List-elim (here refl ∷ xs∈) y∉ = ⊥-elim (proj₁ (y∉⇒All≢ y∉) refl)
   ⊆List-elim (there x∈  ∷ xs∈) y∉
     with y∉⇒All≢ y∉
   ...| x≢y , y∉xs = ∈List-elim (there x∈) x≢y ∷ ⊆List-elim xs∈ y∉xs


   sort→∈-disj : ∀ {n} {x y} {xs ys : List (Fin n)}
               → IsSorted _<Fin_ (x ∷ xs) → IsSorted _<Fin_ (y ∷ ys)
               → x ∈ ys
               → y ∉ xs
   sort→∈-disj (x< ∷ sxs) (on-∷ y<y₁ ∷ sys) x∈ys y∈xs
     = let y₁≤x = ≤-head x∈ys sys
           y<x  = <-transˡ y<y₁ y₁≤x
       in h∉t (trans-OnHead x< y<x ∷ sxs) y∈xs


   sum-⊆-≤ : ∀ {xs ys : List Member} (f : Member → ℕ)
           → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
           → xs ⊆List ys
           → sum (List-map f xs) ≤ sum (List-map f ys)
   sum-⊆-≤ {[]} f sxs sys [] = z≤n
   sum-⊆-≤ {x ∷ _} f (x₁ ∷ sxs) (y₁ ∷ sys) (here refl ∷ xs∈)
     = let xs∈ys = ⊆List-elim xs∈ (h∉t (x₁ ∷ sxs))
       in +-monoʳ-≤ (f x) (sum-⊆-≤ f sxs sys xs∈ys)
   sum-⊆-≤ {_ ∷ _} {y ∷ _} f (x₁ ∷ sxs) (y₁ ∷ sys) (there px ∷ xs∈)
     = let y∉xs  = sort→∈-disj (x₁ ∷ sxs) (y₁ ∷ sys) px
           xs∈ys = ⊆List-elim xs∈ y∉xs
       in ≤-stepsˡ (f y) (sum-⊆-≤ f (x₁ ∷ sxs) sys (px ∷ xs∈ys))


   map-suc-sort : ∀ {n} {xs : List (Fin n)}
                → IsSorted _<Fin_ xs
                → IsSorted _<Fin_ (List-map suc xs)
   map-suc-sort [] = []
   map-suc-sort (x ∷ []) = [] ∷ []
   map-suc-sort (on-∷ x< ∷ (x₁ ∷ sxs)) = (on-∷ (s≤s x<)) ∷ (map-suc-sort (x₁ ∷ sxs))


   tabulateSort : ∀ (n : ℕ) → IsSorted _<Fin_ (List-tabulate {0ℓ} {Fin n} id)
   tabulateSort zero = []
   tabulateSort (suc zero) = [] ∷ []
   tabulateSort (suc (suc n)) =
     let rec      = tabulateSort (suc n)
         sortSuc  = map-suc-sort rec
         map∘Tab≡ = map-tabulate id suc
     in (on-∷ (s≤s z≤n)) ∷ (subst (IsSorted _<Fin_) map∘Tab≡ sortSuc)


   members⊆ : ∀ (xs : List Member) → xs ⊆List participants
   members⊆ [] = []
   members⊆ (x ∷ xs) = Any-tabulate⁺ x refl ∷ (members⊆ xs)


   votingPower≤N : ∀ {xs : List Member} → IsSorted _<Fin_ xs
                 → CombinedPower xs ≤ N
   votingPower≤N {xs} sxs rewrite totalVotPower
     = sum-⊆-≤ votPower sxs (tabulateSort authorsN) (members⊆ xs)


   union-votPower : ∀ {xs ys : List Member}
                      → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                      → CombinedPower (union xs ys) ≤ N
   union-votPower sxs sys = votingPower≤N (unionSorted sxs sys)


   union-∈ : ∀ {xs} {x} (ys : List Member)
           → x ∈ xs → x ∈ union xs ys
   union-∈ [] x∈xs = x∈xs
   union-∈ (y ∷ ys) x∈xs = unionElem-∈ (union-∈ ys x∈xs)
     where unionElem-∈ : ∀ {xs : List Member} {x y} → x ∈ xs
                         → x ∈ unionElem xs y
           unionElem-∈ {x₁ ∷ _} {_} {y} (here px)
             with Fin-<-cmp x₁ y
           ...| tri< _ _ _ = here px
           ...| tri≈ _ _ _ = here px
           ...| tri> _ _ _ = there (here px)
           unionElem-∈ {x₁ ∷ _} {_} {y} (there x∈xs)
             with Fin-<-cmp x₁ y
           ...| tri< _ _ _ = there (unionElem-∈ x∈xs)
           ...| tri≈ _ _ _ = there x∈xs
           ...| tri> _ _ _ = there (there x∈xs)


   unionElem-∈-disj : ∀ {x y} (xs : List Member)
                    → y ∈ unionElem xs x
                    → y ≡ x ⊎ y ∈ xs
   unionElem-∈-disj [] (here px) = inj₁ px
   unionElem-∈-disj {x} (x₁ ∷ xs) y∈
     with Fin-<-cmp x₁ x | y∈
   ...| tri≈ ¬a b ¬c     | y∈∪         = inj₂ y∈∪
   ...| tri> ¬a ¬b c     | (here px)   = inj₁ px
   ...| tri> ¬a ¬b c     | (there y∈∪) = inj₂ y∈∪
   ...| tri< a ¬b ¬c     | (here px)   = inj₂ (here px)
   ...| tri< a ¬b ¬c     | (there y∈∪)
     with unionElem-∈-disj xs y∈∪
   ...| inj₁ y≡x  = inj₁ y≡x
   ...| inj₂ y∈xs = inj₂ (there y∈xs)


   union-∈-disj : ∀ {y} (xs ys : List Member)
                → y ∈ union xs ys
                → y ∈ xs ⊎ y ∈ ys
   union-∈-disj _ [] y∈ = inj₁ y∈
   union-∈-disj xs (y ∷ ys) y∈
     with unionElem-∈-disj (union xs ys) y∈
   ...| inj₁ y≡x = inj₂ (here y≡x)
   ...| inj₂ y∈un
     with union-∈-disj xs ys y∈un
   ...| inj₁ y∈xs = inj₁ y∈xs
   ...| inj₂ y∈ys = inj₂ (there y∈ys)


   union-∉ : ∀ {ys xs : List Member} {y}
           → y ∉ ys → y ∉ xs
           → y ∉ union xs ys
   union-∉ {ys} {xs} y∉ys y∉xs y∈union
     with union-∈-disj xs ys y∈union
   ...| inj₁ y∈xs = ⊥-elim (y∉xs y∈xs)
   ...| inj₂ y∈ys = ⊥-elim (y∉ys y∈ys)


   unionElem-∈-≡ : ∀ {xs : List Member} {x}
                 → x ∈ xs → IsSorted _<Fin_ xs
                 → unionElem xs x ≡ xs
   unionElem-∈-≡ {x₁ ∷ x_} {.x₁} (here refl) _
      with Fin-<-cmp x₁ x₁
   ...| tri< _ ¬b _ = ⊥-elim (¬b refl)
   ...| tri≈ _ _ _  = refl
   ...| tri> _ ¬b _  = ⊥-elim (¬b refl)
   unionElem-∈-≡ {x₁ ∷ _} {x} (there x∈xs) (x₂ ∷ sxs)
      with Fin-<-cmp x₁ x
   ...| tri< _ _ _ = cong (x₁ ∷_) (unionElem-∈-≡ x∈xs sxs)
   ...| tri≈ _ _ _ = refl
   ...| tri> _ _ c = ⊥-elim (<⇒≱ c (≤-head (there x∈xs) (x₂ ∷ sxs)))


   unionElem-∉-sum : ∀ {xs : List Member} {x} (f : Member → ℕ) → x ∉ xs
                   → sum (List-map f (unionElem xs x)) ≡ f x + sum (List-map f xs)
   unionElem-∉-sum {[]}      {_} _ _ = refl
   unionElem-∉-sum {x₁ ∷ xs} {x} f x∉xs
      with Fin-<-cmp x₁ x
   ...| tri< _ _ _ rewrite unionElem-∉-sum f ((proj₂ (y∉⇒All≢ x∉xs)))
                           | sym (+-assoc (f x) (f x₁) (sum (List-map f xs)))
                           | +-comm (f x) (f x₁)
                           | +-assoc (f x₁) (f x) (sum (List-map f xs)) = refl
   ...| tri≈ _ b _ = ⊥-elim (proj₁ (y∉⇒All≢ x∉xs) b)
   ...| tri> _ _ _ = refl


   sumIntersect≤ : ∀ {xs ys : List Member} (f : Member → ℕ)
                 → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
                 → sum (List-map f (intersect xs ys)) ≤ sum (List-map f (xs ++ ys))
   sumIntersect≤ {_} {[]} _ _ _ = z≤n
   sumIntersect≤ {xs} {y ∷ ys} f sxs (_ ∷ sys)
     with y ∈? xs
   ...| yes y∈xs rewrite intersectElem-∈-≡ y∈xs sxs
                       | map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | sym (+-assoc (sum (List-map f xs)) (f y) (sum (List-map f ys)))
                       | +-comm (sum (List-map f xs)) (f y)
                       | +-assoc (f y) (sum (List-map f xs)) (sum (List-map f ys))
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = +-monoʳ-≤ (f y) (sumIntersect≤ f sxs sys)
   ...| no  y∉xs rewrite intersectElem-∉-[] y∉xs
                       | map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | +-comm (f y) (sum (List-map f ys))
                       | sym (+-assoc (sum (List-map f xs)) (sum (List-map f ys)) (f y))
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = ≤-stepsʳ (f y) (sumIntersect≤ f sxs sys)


   union-votPower≡ :  ∀ {xs ys : List Member}
                      → (sxs : IsSorted _<Fin_ xs) → (sys : IsSorted _<Fin_ ys)
                      → CombinedPower (union xs ys) ≡ CombinedPower (xs ++ ys)
                                                    ∸ CombinedPower (intersect xs ys)
   union-votPower≡ {xs} {[]} _ _
     rewrite map-++-commute votPower xs []
           | sum-++-commute (List-map votPower xs) []
           | +-identityʳ (CombinedPower xs) = refl
   union-votPower≡ {xs} {y ∷ ys} sxs (y₁ ∷ sys)
      with y ∈? xs
   ...| yes y∈xs rewrite unionElem-∈-≡ (union-∈ ys y∈xs) (unionSorted sxs sys)
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
                       | intersectElem-∉-[] y∉xs
                       | +-assoc (votPower y)
                                 (CombinedPower xs)
                                 (CombinedPower ys)
                       | sym (sum-++-commute (List-map votPower xs) (List-map votPower ys))
                       | sym (map-++-commute votPower xs ys)
                       | +-∸-assoc (votPower y) (sumIntersect≤ votPower sxs sys) = refl


   quorumInt>biz : ∀ (xs ys : List Member)
                 → QSize ≤ CombinedPower xs
                 → QSize ≤ CombinedPower ys
                 → CombinedPower (xs ++ ys) ∸ N ≤ CombinedPower (intersect xs ys)
                 → bizF + 1 ≤ CombinedPower (intersect xs ys)
   quorumInt>biz xs ys q≤x q≤y ≤int
     rewrite map-++-commute votPower xs ys
           | sum-++-commute (List-map votPower xs) (List-map votPower ys)
           = let powInt = CombinedPower (intersect xs ys)
                 q₁≥n∸f = ≤-trans quorumVotPower q≤x
                 q₂≥n∸f = ≤-trans quorumVotPower q≤y
                 p₁     = ≤-trans (∸-monoˡ-≤ N (+-mono-≤ q₁≥n∸f q₂≥n∸f)) ≤int
                 p₂     = subst (_≤ powInt) (simpExp₁ N bizF) p₁
                 p₃     = ≤-trans (∸-monoˡ-≤ (2 * bizF) isBFT) p₂
             in subst (_≤ powInt) (simpExp₂ bizF) p₃
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
                               | sym (+-suc x 0) = refl


   span-hon : ∀ {xs dis hon : List Member} {x : Member}
            → span Meta-dishonest? xs ≡ (dis , x ∷ hon)
            → x ∈ xs ×  Meta-Honest-PK (getPubKey x)
   span-hon {x ∷ xs} eq
     with Meta-dishonest? x | eq
   ...| no imp  | refl = here refl , imp
   ...| yes _   | eq₁
     with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| _ , x₂ ∷ _ | [ eq₂ ] rewrite just-injective (cong (head ∘ proj₂) eq₁)
     = ×-map₁ there (span-hon eq₂)


   span-dis : ∀ {xs dis : List Member}
            → span Meta-dishonest? xs ≡ (dis , [])
            → List-filter Meta-dishonest? xs ≡ xs
   span-dis {[]} _ = refl
   span-dis {x ∷ xs} span≡
      with Meta-dishonest? x | span≡
   ...| no ¬dis  | ()
   ...| yes _  | _
      with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| _ , [] | [ eq₁ ] = cong (x ∷_) (span-dis {xs} eq₁)


   -- TODO-1 : An alternative to prove this lemma would be:
   -- - First prove that
   --   CombinedPower (List-filter Meta-dishonest? xs) ≤ CombinedPower xs.
   -- - Then prove that:
   --   - If CombinedPower (List-filter Meta-dishonest? xs) ≤ CombinedPower xs
   --     then ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α)).
   --   - If CombinedPower (List-filter Meta-dishonest? xs ≡ CombinedPower xs we
   --   get a contradiction using the bft assumption (as we have now).
   find-honest : ∀ {xs : List Member}
               → IsSorted _<Fin_ xs
               → bizF + 1 ≤ CombinedPower xs
               → ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α))
   find-honest {xs} sxs biz<
     with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| dis , [] | [ eq ]
        rewrite +-comm bizF 1
          = let bft     = bft-assumption sxs
                xsVot≤f = subst (_≤ bizF) (cong CombinedPower (span-dis {xs} eq)) bft
            in ⊥-elim (<⇒≱ biz< xsVot≤f)
   ...| dis , x ∷ hon | [ eq ] = x , (span-hon eq)


   bft-lemma : {xs ys : List Member}
             -- enforcing both xs and ys to be sorted lists according to
             -- a anti-reflexive linear order ensures authors are distinct.
             → IsSorted _<Fin_ xs → IsSorted _<Fin_ ys
             → QSize ≤ CombinedPower xs
             → QSize ≤ CombinedPower ys
             → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-PK (getPubKey α))
   bft-lemma {xs} {ys} sxs sys q≤xs q≤ys
     = let |q₁|+|q₂|   = CombinedPower (xs ++ ys)
           |q₁∩q₂|     = CombinedPower (intersect xs ys)
           |q₁∪q₂|≤n   = union-votPower sxs sys
           exp₁        = subst (_≤ N) (union-votPower≡ sxs sys) |q₁∪q₂|≤n
           exp₂        = m∸n≤o⇒m∸o≤n |q₁|+|q₂| |q₁∩q₂| N exp₁
           f+1≤|q₁∩q₂| = quorumInt>biz xs ys q≤xs q≤ys exp₂
           honInf      = find-honest (intersectDiff sxs sys) f+1≤|q₁∩q₂|
           h∈∩         = ∈-intersect sxs sys ((proj₁ ∘ proj₂) honInf)
       in proj₁ honInf , proj₁ h∈∩ , proj₂ h∈∩ , (proj₂ ∘ proj₂) honInf



