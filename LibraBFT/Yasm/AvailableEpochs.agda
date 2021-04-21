{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
import      Data.Vec.Relation.Unary.All as Vec-All
import      Data.Fin                    as Fin

-- This module defines the EpochConfigs available in the system, along
-- with a function to add a new EpochConfig and some properties that
-- facilitate proofs across state transitions that add an EpochConfig.

module LibraBFT.Yasm.AvailableEpochs
   (NodeId      : Set)
   (ℓ-EC        : Level)
   (EpochConfig : Set ℓ-EC)
   (epoch       : EpochConfig → ℕ)
   (authorsN    : EpochConfig → ℕ)
 where
 open import LibraBFT.Yasm.Base ℓ-EC EpochConfig epoch authorsN

 fin-lower-toℕ : ∀{e}(i : Fin (suc e))(prf : e ≢ toℕ i) → toℕ (Fin.lower₁ i prf) ≡ toℕ i
 fin-lower-toℕ {zero} zero prf = ⊥-elim (prf refl)
 fin-lower-toℕ {suc e}  zero prf = refl
 fin-lower-toℕ {suc e} (suc i) prf = cong suc (fin-lower-toℕ i (prf ∘ cong suc))

 toℕ-correct : ∀{n}(i : Fin n) → toℕ i < n
 toℕ-correct zero = s≤s z≤n
 toℕ-correct (suc i) = s≤s (toℕ-correct i)

 toℕ-inject₁-≡ : ∀{n}(i : Fin n) → toℕ i ≡ toℕ (Fin.inject₁ i)
 toℕ-inject₁-≡ zero = refl
 toℕ-inject₁-≡ (suc i) = cong suc (toℕ-inject₁-≡ i)

 lower₁-inject₁-id : ∀{n}(i : Fin n)(prf : n ≢ toℕ (Fin.inject₁ i)) → Fin.lower₁ (Fin.inject₁ i) prf ≡ i
 lower₁-inject₁-id zero prf = refl
 lower₁-inject₁-id (suc i) prf = cong suc (lower₁-inject₁-id i (prf ∘ cong suc))

 fromℕ-≤-step-natural : ∀{n m}(prf : n < m) → fromℕ< (≤-step prf) ≡ Fin.inject₁ (fromℕ< prf)
 fromℕ-≤-step-natural (s≤s z≤n) = refl
 fromℕ-≤-step-natural (s≤s (s≤s prf)) = cong suc (fromℕ-≤-step-natural (s≤s prf))


 Vec-All-lookup∘tabulate : ∀{n}{A : Set}{v : Vec A n}{ℓ : Level}{P : A → Set ℓ}
                         → (f : (x : Fin n) → P (Vec-lookup v x))(i : Fin n)
                         → Vec-All.lookup {P = P} i (Vec-All.tabulate {xs = v} f) ≡ f i
 Vec-All-lookup∘tabulate {v = v₀ ∷ vs} f zero = refl
 Vec-All-lookup∘tabulate {v = v₀ ∷ vs} f (suc i) = Vec-All-lookup∘tabulate (f ∘ suc) i

 subst-elim : {A : Set}{ℓ : Level}(P : A → Set ℓ){a₀ a₁ : A}
            → (prf : a₀ ≡ a₁)(x : P a₁)
            → subst P prf (subst P (sym prf) x) ≡ x
 subst-elim _ refl x = refl

 -- Available epochs consist of a vector of EpochConfigs with
 -- the correct epoch ids.
 AvailableEpochs : ℕ → Set ℓ-EC
 AvailableEpochs = Vec-All (EpochConfigFor ∘ toℕ) ∘ Vec-allFin

 lookup : ∀{e} → AvailableEpochs e → (ix : Fin e) → EpochConfigFor (toℕ ix)
 lookup 𝓔s ix =  subst EpochConfigFor (cong toℕ (Vec-lookup∘tabulate id ix)) (Vec-All-lookup ix 𝓔s)

 lookup' : ∀{e} → AvailableEpochs e → Fin e → EpochConfig
 lookup' 𝓔s ix = EpochConfigFor.epochConfig (lookup 𝓔s ix)

 lookup'' : ∀{e m} → AvailableEpochs e → m < e → EpochConfig
 lookup'' 𝓔s ix = lookup' 𝓔s (fromℕ< ix)

 lookup-𝓔s-injective : ∀ {e m1 m2} → (𝓔s : AvailableEpochs e)
                     → (p1 : m1 < e) → (p2 : m2 < e) → m1 ≡ m2
                     → lookup'' 𝓔s p1 ≡ lookup'' 𝓔s p2
 lookup-𝓔s-injective {e} 𝓔s p1 p2 refl = cong (lookup'' 𝓔s) (<-irrelevant p1 p2)

 -- The /transpose/ of append is defined by the semantics of a lookup
 -- over an append; the /append/ function below is defined by tabulating this
 -- monster.
 appendᵀ : ∀{e} → EpochConfigFor e → AvailableEpochs e → (i : Fin (suc e)) → EpochConfigFor (toℕ i)
 appendᵀ {e} ecf al i with e ≟ℕ toℕ i
 ...| yes e≡i = subst EpochConfigFor e≡i ecf
 ...| no  prf = subst EpochConfigFor
                      (trans (cong toℕ (Vec-lookup∘tabulate id (Fin.lower₁ i prf)))
                             (fin-lower-toℕ i prf))
                      (Vec-All-lookup (Fin.lower₁ i prf) al)

 -- Append is defined by tabulating appendᵀ
 append : ∀{e} → EpochConfigFor e → AvailableEpochs e → AvailableEpochs (suc e)
 append {e} ecf al = Vec-All.tabulate
    (λ i → subst (EpochConfigFor) (sym (cong toℕ (Vec-lookup∘tabulate id i))) (appendᵀ ecf al i))

 lookup-append-lemma
   : ∀{e}(𝓔s : AvailableEpochs e)(𝓔 : EpochConfigFor e)(ix : Fin (suc e))
   → lookup (append 𝓔 𝓔s) ix ≡ appendᵀ 𝓔 𝓔s ix
 lookup-append-lemma al ecf ix
   rewrite Vec-All-lookup∘tabulate
          {v = zero ∷ Vec-tabulate suc}
          {P = EpochConfigFor ∘ toℕ}
          (λ i → subst EpochConfigFor (sym (cong toℕ (Vec-lookup∘tabulate id i))) (appendᵀ ecf al i)) ix
        = subst-elim EpochConfigFor (cong toℕ (Vec-lookup∘tabulate id ix)) (appendᵀ ecf al ix)

 -- Ok, let's bring in the big guns
 import Relation.Binary.HeterogeneousEquality as HE

 append-inject₁-lemma
   : ∀{e}(𝓔s : AvailableEpochs e)(𝓔 : EpochConfigFor e)(ix : Fin e)
   → appendᵀ 𝓔 𝓔s (Fin.inject₁ ix)
   ≅ lookup 𝓔s ix
 append-inject₁-lemma {e} 𝓔s 𝓔 ix
   with e ≟ℕ (toℕ (Fin.inject₁ ix))
 ...| yes abs = ⊥-elim (<⇒≢ (toℕ-correct ix) (trans (toℕ-inject₁-≡ ix) (sym abs)))
 ...| no  prf = HE.trans (HE.≡-subst-removable EpochConfigFor
                           (trans (cong toℕ (Vec-lookup∘tabulate id (Fin.lower₁ (Fin-inject₁ ix) prf)))
                                  (fin-lower-toℕ (Fin.inject₁ ix) prf))
                           (Vec-All-lookup (Fin.lower₁ (Fin.inject₁ ix) prf) 𝓔s))
               (HE.trans (≅-cong (λ P → Vec-All-lookup P 𝓔s) (HE.≡-to-≅ (lower₁-inject₁-id ix prf)))
                         (HE.sym (HE.≡-subst-removable EpochConfigFor
                                   (cong toℕ (Vec-lookup∘tabulate id ix))
                                   (Vec-All-lookup ix 𝓔s))))

 lookup''-≤-step-lemma
   : ∀{e m}(𝓔s : AvailableEpochs e)(𝓔 : EpochConfigFor e)(prf : m < e)
   → lookup'' (append 𝓔 𝓔s) (≤-step prf) ≡ lookup'' 𝓔s prf
 lookup''-≤-step-lemma al ecf prf
   rewrite fromℕ-≤-step-natural prf
         | lookup-append-lemma al ecf (Fin.inject₁ (fromℕ< prf))
         = ECF-cong (append-inject₁-lemma al ecf (fromℕ< prf))
                    (sym (toℕ-inject₁-≡ (fromℕ< prf)))
   where
    ECF-cong : ∀{e e'}{ef : EpochConfigFor e}{ef' : EpochConfigFor e'}
             → ef ≅ ef' → e ≡ e'
             → EpochConfigFor.epochConfig ef ≡ EpochConfigFor.epochConfig ef'
    ECF-cong {e} {e'} {ef} {ef'} HE.refl refl = refl
