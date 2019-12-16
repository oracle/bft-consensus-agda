{--

This shows that the HashSet postulates as of commit ec5361c are self-contradictory if hash
collisions exist (this is proved via a silly hash function that trivially has collisions, but
because hashes are fixed size, we can prove that hash collisions always exist for large enough
sets).

--}


open import Data.Nat
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Prelude hiding (lookup)

module LibraBFT.Concrete.Util.HashSetTest where

  sillyHash : ℕ → Hash
  sillyHash x with x ≤?ℕ 2
  ...| yes x≤2 = (replicate 32 true  , refl)
  ...| no x>2  = (replicate 32 false , refl)

  hashColl01 : sillyHash 0 ≡ sillyHash 1
  hashColl01 = refl

  open import LibraBFT.Concrete.Util.HashSet {ℕ} sillyHash

  with0 : HashSet
  with0 = hs-insert 0 empty (∈HS-empty-⊥)

  0∈with0 : 0 ∈HS with0
  0∈with0 = hs-insert-∈HS 0 empty (∈HS-empty-⊥)

  aux : ¬ 1 ≡ 0
  aux ()

  oops : ⊥
  oops with 1 ∈HS? with0
  ...| yes xx = aux (hs-insert-target (∈HS-empty-⊥ {0}) (∈HS-empty-⊥ {1}) xx)
  ...| no xx  = maybe-⊥ {x = 0}{y = lookup with0 (sillyHash 0)}
                 (∈HS-correct 0 with0 0∈with0)
                 (trans (cong (lookup with0) hashColl01) (∉HS-correct 1 with0 xx))
