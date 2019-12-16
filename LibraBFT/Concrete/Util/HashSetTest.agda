{--

This shows that the HashSet postulates as of commit 8203427 are still self-contradictory if hash
collisions exist (this is proved via a silly hash function that trivially has collisions, but
because hashes are fixed size, we can prove that hash collisions always exist for large enough
sets).

The problem is that ∈HS-correct k and ∉HS-correct k together imply that there is no k' such that k'
≢ k and hashK k′ ≡ hashK k, but of course this is not the case if there are hash collisions.  In the
next commit I am weakening ∉HS-correct to eliminate this problem.

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

  k-empty-lookup : ∀ {k} → lookup empty (sillyHash k) ≡ nothing
  k-empty-lookup {k} = ∉HS-correct k empty ∈HS-empty-⊥

  with0 : HashSet
  with0 = hs-insert 0 empty (k-empty-lookup {0})

  0∈with0 : 0 ∈HS with0
  0∈with0 = hs-insert-∈HS 0 empty (∉HS-correct 0 empty ∈HS-empty-⊥)

  aux : ¬ 1 ≡ 0
  aux ()

  oops : ⊥
  oops with 1 ∈HS? with0
  ...| yes xx = aux (hs-insert-target (k-empty-lookup {0}) ∈HS-empty-⊥ xx)
  ...| no xx  = maybe-⊥ {x = 0}{y = lookup with0 (sillyHash 0)}
                 (∈HS-correct 0 with0 0∈with0)
                 (trans (cong (lookup with0) hashColl01) (∉HS-correct 1 with0 xx))
