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
  -- participants can have different voting power.

  -- The module is parametrized with the number of participants -
  -- `authorsN`, and with a function - `votPower` - that assigns to
  -- each participant its voting power. The parameter `N` corresponds
  -- to the total voting power of all participants, as required by the
  -- parameter `totalVotPower` in the inner module. These
  -- implementations should assume a fixed unknown subset of malicious
  -- nodes - Byzantine - but should also assume a security threshold
  -- `bizF`, such that N > 3 * bizF, which should be provided in
  -- parameter `isBFT`.  Finally, the `bft-assumption` states that the
  -- combined voting power of Byzantine nodes must not exceed the
  -- security threshold `bizF`.

  -- The bft-lemma is the last lemma in this file and proves that in
  -- the intersection of any quorums, whose combined voting power is
  -- greater or equal than `N - bizF`, there is an honest Member.

module LibraBFT.Abstract.BFT
  (authorsN      : ℕ)
  (votPower      : Fin authorsN → ℕ)
  (totalVotPower : ℕ)
  (bizF          : ℕ)
  (isBFT         : totalVotPower ≥ suc (3 * bizF))
  (getPubKey     : Fin authorsN → PK)


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
 -- `bizF`. Therefore, for any list of distinct participants, the
 -- combined power of the dishonest nodes is less or equal than
 -- `bizF`. To express a list of distinct particpants we used the data
 -- type `IsSorted _<Fin_`, enforcing xs to be sorted according to a
 -- anti-reflexive linear order ensures authors are distinct.

 -- TODO-1 : Replace `IsSorted _<Fin_ xs` with the type `allDistinct`
 -- in `LibraBFT.Lemmas

 module _  (totalVotPower≡  : totalVotPower ≡ CombinedPower (List-tabulate id))
           (bft-assumption : ∀ (xs : List Member)
                           → allDistinct xs
                           → CombinedPower (List-filter Meta-dishonest? xs) ≤ bizF)
   where

   participants : List Member
   participants = List-tabulate id

   -- TODO-2 : Many of these lemmas can be generalized for any list or any
   -- list of Fin. Perhaps establish a Lemmas.FinProps module.

   intersect : ∀ {n} → List (Fin n) → List (Fin n) → List (Fin n)
   intersect xs [] = []
   intersect xs (y ∷ ys)
     with y ∈? xs
   ...| yes _ = y ∷ intersect xs ys
   ...| no  _ = intersect xs ys


   union :  ∀ {n} → List (Fin n) → List (Fin n) → List (Fin n)
   union xs [] = xs
   union xs (y ∷ ys)
     with y ∈? xs
   ...| yes _ = union xs ys
   ...| no  _ = y ∷ union xs ys


   int-[]≡[] : (xs : List Member) → intersect [] xs ≡ []
   int-[]≡[] [] = refl
   int-[]≡[] (x ∷ xs) = int-[]≡[] xs


   ∈-intersect : ∀ (xs ys : List Member) {α}
               → α ∈ intersect xs ys
               → α ∈ xs × α ∈ ys
   ∈-intersect xs (y ∷ ys) α∈int
     with y ∈? xs  | α∈int
   ...| no  y∉xs   | α∈        = ×-map₂ there (∈-intersect xs ys α∈)
   ...| yes y∈xs   | here refl = y∈xs , here refl
   ...| yes y∈xs   | there α∈  = ×-map₂ there (∈-intersect xs ys α∈)


   morgan₁ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
   morgan₁ (inj₁ ¬a) = λ a×b → ¬a (proj₁ a×b)
   morgan₁ (inj₂ ¬b) = λ a×b → ¬b (proj₂ a×b)


   x∉⇒x∉intersect : ∀ {x} {xs ys : List Member}
                    → x ∉ xs ⊎ x ∉ ys
                    → x ∉ intersect xs ys
   x∉⇒x∉intersect {x} {xs} {ys} x∉ x∈int
     = contraposition (∈-intersect xs ys) (morgan₁ x∉) x∈int


   intersectDistinct : ∀ (xs ys : List Member)
                     → allDistinct xs → allDistinct ys
                     → allDistinct (intersect xs ys)
   intersectDistinct xs (y ∷ ys) dxs dys
     with y ∈? xs
   ...| yes y∈xs = let distTail  = allDistinctTail dys
                       intDTail  = intersectDistinct xs ys dxs distTail
                       y∉intTail = x∉⇒x∉intersect (inj₂ (allDistinct⇒∉ dys))
                   in x∉→AllDistinct intDTail y∉intTail
   ...| no  y∉xs = intersectDistinct xs ys dxs (allDistinctTail dys)


   x∉⇒x∉union : ∀ {x} {xs ys : List Member}
              → x ∉ xs × x ∉ ys
              → x ∉ union xs ys
   x∉⇒x∉union {_} {_} {[]} (x∉xs , _) x∈∪ = ⊥-elim (x∉xs x∈∪)
   x∉⇒x∉union {x} {xs} {y ∷ ys} (x∉xs , x∉ys) x∈union
     with y ∈? xs  | x∈union
   ...| yes y∈xs   | x∈∪
        = ⊥-elim (x∉⇒x∉union (x∉xs , (proj₂ (y∉xs⇒Allxs≢y x∉ys))) x∈∪)
   ...| no y∉xs    | here refl
        = ⊥-elim (proj₁ (y∉xs⇒Allxs≢y x∉ys) refl)
   ...| no y∉xs    | there x∈∪
        = ⊥-elim (x∉⇒x∉union (x∉xs , (proj₂ (y∉xs⇒Allxs≢y x∉ys))) x∈∪)

   unionDistinct : ∀ (xs ys : List Member)
               → allDistinct xs → allDistinct ys
               → allDistinct (union xs ys)
   unionDistinct xs [] dxs dys = dxs
   unionDistinct xs (y ∷ ys) dxs dys
      with y ∈? xs
   ...| yes y∈xs = unionDistinct xs ys dxs (allDistinctTail dys)
   ...| no  y∉xs = let distTail  = allDistinctTail dys
                       uniDTail  = unionDistinct xs ys dxs distTail
                       y∉intTail = x∉⇒x∉union (y∉xs , allDistinct⇒∉ dys)
                   in x∉→AllDistinct uniDTail y∉intTail


   members⊆ : ∀ {xs : List Member} → xs ⊆List participants
   members⊆ {_} {x} _ = Any-tabulate⁺ {f = id} x refl


   votingPower≤N : ∀ (xs : List Member) → allDistinct xs
                 → CombinedPower xs ≤ totalVotPower
   votingPower≤N xs dxs rewrite totalVotPower≡
     = sum-⊆-≤ xs votPower dxs members⊆


   union-votPower : ∀ (xs ys : List Member)
                  → allDistinct xs → allDistinct ys
                  → CombinedPower (union xs ys) ≤ totalVotPower
   union-votPower xs ys dxs dys
     = votingPower≤N (union xs ys) (unionDistinct xs ys dxs dys)


   sumIntersect≤ : ∀ {n} (xs ys : List (Fin n)) (f : Fin n → ℕ)
                 → sum (List-map f (intersect xs ys)) ≤ sum (List-map f (xs ++ ys))
   sumIntersect≤ _ [] _ = z≤n
   sumIntersect≤ xs (y ∷ ys) f
     with y ∈? xs
   ...| yes y∈xs rewrite map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | sym (+-assoc (sum (List-map f xs)) (f y) (sum (List-map f ys)))
                       | +-comm (sum (List-map f xs)) (f y)
                       | +-assoc (f y) (sum (List-map f xs)) (sum (List-map f ys))
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = +-monoʳ-≤ (f y) (sumIntersect≤ xs ys f)
   ...| no  y∉xs rewrite map-++-commute f xs (y ∷ ys)
                       | sum-++-commute (List-map f xs) (List-map f (y ∷ ys))
                       | +-comm (f y) (sum (List-map f ys))
                       | sym (+-assoc (sum (List-map f xs)) (sum (List-map f ys)) (f y))
                       | sym (sum-++-commute (List-map f xs) (List-map f ys))
                       | sym (map-++-commute f xs ys)
                         = ≤-stepsʳ (f y) (sumIntersect≤ xs ys f)


   union-votPower≡ :  ∀ (xs ys : List Member)
                      → allDistinct xs → allDistinct ys
                      → CombinedPower (union xs ys) ≡ CombinedPower (xs ++ ys)
                                                    ∸ CombinedPower (intersect xs ys)
   union-votPower≡ xs [] dxs dys rewrite ++-identityʳ xs = refl
   union-votPower≡ xs (y ∷ ys) dxs dys
     with y ∈? xs
   ...| yes y∈xs rewrite union-votPower≡ xs ys dxs (allDistinctTail dys)
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
                       | sym (sum-++-commute (List-map votPower xs) (List-map votPower (y ∷ ys)))
                       | sym (map-++-commute votPower xs (y ∷ ys)) = refl
   ...| no  y∉xs rewrite union-votPower≡ xs ys dxs (allDistinctTail dys)
                       | sym (+-∸-assoc (votPower y) (sumIntersect≤ xs ys votPower))
                       | map-++-commute votPower xs ys
                       | sum-++-commute (List-map votPower xs) (List-map votPower ys)
                       | sym (+-assoc (votPower y) (CombinedPower xs) (CombinedPower ys))
                       | +-comm (votPower y) (CombinedPower xs)
                       | +-assoc (CombinedPower xs) (votPower y) (CombinedPower ys)
                       | sym (sum-++-commute (List-map votPower xs) (List-map votPower (y ∷ ys)))
                       | sym (map-++-commute votPower xs (y ∷ ys)) = refl


   quorumInt>biz : ∀ (xs ys : List Member)
                 → totalVotPower ∸ bizF ≤ CombinedPower xs
                 → totalVotPower ∸ bizF ≤ CombinedPower ys
                 → CombinedPower (xs ++ ys) ∸ totalVotPower ≤ CombinedPower (intersect xs ys)
                 → bizF + 1 ≤ CombinedPower (intersect xs ys)
   quorumInt>biz xs ys q≤x q≤y ≤combPower
     rewrite map-++-commute votPower xs ys
           | sum-++-commute (List-map votPower xs) (List-map votPower ys)
           = let powInt = CombinedPower (intersect xs ys)
                 p₁     = ≤-trans (∸-monoˡ-≤ totalVotPower (+-mono-≤ q≤x q≤y)) ≤combPower
                 p₂     = subst (_≤ powInt) (simpExp₁ totalVotPower bizF) p₁
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
               → allDistinct xs
               → bizF + 1 ≤ CombinedPower xs
               → ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α))
   find-honest {xs} sxs biz<
     with span Meta-dishonest? xs | inspect (span Meta-dishonest?) xs
   ...| dis , [] | [ eq ]
        rewrite +-comm bizF 1
          = let bft     = bft-assumption xs sxs
                xsVot≤f = subst (_≤ bizF) (cong CombinedPower (span-dis {xs} eq)) bft
            in ⊥-elim (<⇒≱ biz< xsVot≤f)
   ...| dis , x ∷ hon | [ eq ] = x , (span-hon eq)


   bft-lemma : {xs ys : List Member}
             -- enforcing both xs and ys to be sorted lists according to
             -- a anti-reflexive linear order ensures authors are distinct.
             → allDistinct xs → allDistinct ys
             → totalVotPower ∸ bizF ≤ CombinedPower xs
             → totalVotPower ∸ bizF ≤ CombinedPower ys
             → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-PK (getPubKey α))
   bft-lemma {xs} {ys} all≢xs all≢ys q≤≢xs q≤≢ys
     = let |q₁|+|q₂|   = CombinedPower (xs ++ ys)
           |q₁∩q₂|     = CombinedPower (intersect xs ys)
           |q₁∪q₂|≤n   = union-votPower xs ys all≢xs all≢ys
           |q₁∪q₂|≡    = union-votPower≡ xs ys all≢xs all≢ys
           exp₁        = subst (_≤ totalVotPower) |q₁∪q₂|≡ |q₁∪q₂|≤n
           exp₂        = m∸n≤o⇒m∸o≤n |q₁|+|q₂| |q₁∩q₂| totalVotPower exp₁
           f+1≤|q₁∩q₂| = quorumInt>biz xs ys q≤≢xs q≤≢ys exp₂
           intDist     = intersectDistinct xs ys all≢xs all≢ys
           honInf      = find-honest {intersect xs ys} intDist f+1≤|q₁∩q₂|
           h∈∩         = ∈-intersect xs ys ((proj₁ ∘ proj₂) honInf)
           α∈xs        = proj₁ h∈∩
           α∈ys        = proj₂ h∈∩
       in proj₁ honInf , α∈xs , α∈ys , (proj₂ ∘ proj₂) honInf



