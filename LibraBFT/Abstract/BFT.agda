{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Lemmas
open import LibraBFT.Prelude

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
  -- greater than or equal to `N - bizF`, there is an honest Member.

module LibraBFT.Abstract.BFT
  (authorsN      : ℕ)
  (votPower      : Fin authorsN → ℕ)
  (bizF          : ℕ)
  (isBFT         : f-sum votPower (allFin authorsN) ≥ suc (3 * bizF))
  (getPubKey     : Fin authorsN → PK)
 where

 -- The set of members of this epoch.
 Member : Set
 Member = Fin authorsN

 Meta-dishonest? :  ∀ (m : Member) → Dec (Meta-Dishonest-PK (getPubKey m))
 Meta-dishonest? m = Meta-DishonestPK? (getPubKey m)

 CombinedPower : List Member → ℕ
 CombinedPower = f-sum votPower

 TotalVotPower : ℕ
 TotalVotPower = f-sum votPower (allFin authorsN)

 open DecLemmas {A = Member} _≟Fin_

 -- The bft-assumption states that the combined voting power of
 -- Byzantine nodes must not exceed the security threshold
 -- `bizF`. Therefore, for any list of distinct participants, the
 -- combined power of the dishonest nodes is less than or equal to
 -- `bizF`.
 module _  (bft-assumption : ∀ (xs : List Member)
                           → allDistinct xs
                           → CombinedPower (List-filter Meta-dishonest? xs) ≤ bizF)
   where

   participants : List Member
   participants = allFin authorsN

   members⊆ : ∀ {xs : List Member} → xs ⊆List participants
   members⊆ {_} {x} _ = Any-tabulate⁺ {f = id} x refl

   union-votPower≤N : ∀ (xs ys : List Member)
                  → allDistinct xs → allDistinct ys
                  → CombinedPower (union xs ys) ≤ TotalVotPower
   union-votPower≤N xs ys dxs dys
     = sum-⊆-≤ (union xs ys) votPower (unionDistinct xs ys dxs dys) members⊆

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
                 → TotalVotPower ∸ bizF ≤ CombinedPower xs
                 → TotalVotPower ∸ bizF ≤ CombinedPower ys
                 → CombinedPower (xs ++ ys) ∸ TotalVotPower ≤ CombinedPower (intersect xs ys)
                 → bizF + 1 ≤ CombinedPower (intersect xs ys)
   quorumInt>biz xs ys q≤x q≤y ≤combPower
     rewrite map-++-commute votPower xs ys
           | sum-++-commute (List-map votPower xs) (List-map votPower ys)
           = let powInt = CombinedPower (intersect xs ys)
                 p₁     = ≤-trans (∸-monoˡ-≤ TotalVotPower (+-mono-≤ q≤x q≤y)) ≤combPower
                 p₂     = subst (_≤ powInt) (simpExp₁ TotalVotPower bizF) p₁
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

   partition-hon : ∀ {xs dis hon : List Member} {x : Member}
            → partition Meta-dishonest? xs ≡ (dis , x ∷ hon)
            → x ∈ xs × Meta-Honest-PK (getPubKey x)
   partition-hon {x ∷ xs} eq
     with Meta-dishonest? x | eq
   ...| no imp  | refl = here refl , imp
   ...| yes _   | eq₁
     with partition Meta-dishonest? xs | inspect (partition Meta-dishonest?) xs
   ...| _ , x₂ ∷ _ | [ eq₂ ] rewrite just-injective (cong (head ∘ proj₂) eq₁)
     = ×-map₁ there (partition-hon eq₂)

   partition-dis : ∀ {xs dis : List Member}
            → partition Meta-dishonest? xs ≡ (dis , [])
            → List-filter Meta-dishonest? xs ≡ xs
   partition-dis {[]} _ = refl
   partition-dis {x ∷ xs} eq
      with Meta-dishonest? x | eq
   ...| no ¬dis  | ()
   ...| yes _  | _
      with partition Meta-dishonest? xs | inspect (partition Meta-dishonest?) xs
   ...| _ , [] | [ eq₁ ] = cong (x ∷_) (partition-dis {xs} eq₁)

   -- TODO-1 : An alternative to prove this lemma would be:
   -- - First prove that
   --   CombinedPower (List-filter Meta-dishonest? xs) ≤ CombinedPower xs.
   -- - Then prove that:
   --   - If CombinedPower (List-filter Meta-dishonest? xs) < CombinedPower xs
   --     then ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α)).
   --   - If CombinedPower (List-filter Meta-dishonest? xs ≡ CombinedPower xs we
   --   get a contradiction using the bft assumption (as we have now).
   find-honest : ∀ {xs : List Member}
               → allDistinct xs
               → bizF < CombinedPower xs
               → ∃[ α ] (α ∈ xs × Meta-Honest-PK (getPubKey α))
   find-honest {xs} sxs biz<
     with partition Meta-dishonest? xs | inspect (partition Meta-dishonest?) xs
   ...| dis , [] | [ eq ]
          = let bft     = bft-assumption xs sxs
                xsVot≤f = subst (_≤ bizF) (cong CombinedPower (partition-dis {xs} eq)) bft
            in ⊥-elim (<⇒≱ biz< xsVot≤f)
   ...| dis , x ∷ hon | [ eq ] = x , partition-hon eq

   bft-lemma : {xs ys : List Member}
             → allDistinct xs → allDistinct ys
             → TotalVotPower ∸ bizF ≤ CombinedPower xs
             → TotalVotPower ∸ bizF ≤ CombinedPower ys
             → ∃[ α ] (α ∈ xs × α ∈ ys × Meta-Honest-PK (getPubKey α))
   bft-lemma {xs} {ys} all≢xs all≢ys q≤≢xs q≤≢ys
     = let |q₁|+|q₂|   = CombinedPower (xs ++ ys)
           |q₁∩q₂|     = CombinedPower (intersect xs ys)
           |q₁∪q₂|≤n   = union-votPower≤N xs ys all≢xs all≢ys
           |q₁∪q₂|≡    = union-votPower≡ xs ys all≢xs all≢ys
           exp₁        = subst (_≤ TotalVotPower) |q₁∪q₂|≡ |q₁∪q₂|≤n
           exp₂        = m∸n≤o⇒m∸o≤n |q₁|+|q₂| |q₁∩q₂| TotalVotPower exp₁
           f+1≤|q₁∩q₂| = quorumInt>biz xs ys q≤≢xs q≤≢ys exp₂
           f<|q₁∩q₂|   = subst (_≤ |q₁∩q₂|) (+-comm bizF 1) f+1≤|q₁∩q₂|
           intDist     = intersectDistinct xs ys all≢xs all≢ys
           honInf      = find-honest {intersect xs ys} intDist f<|q₁∩q₂|
           h∈∩         = ∈-intersect xs ys ((proj₁ ∘ proj₂) honInf)
       in proj₁ honInf ,  proj₁ h∈∩ , proj₂ h∈∩ , (proj₂ ∘ proj₂) honInf


