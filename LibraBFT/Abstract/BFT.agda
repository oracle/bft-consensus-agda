{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.BFT
    (𝓔      : EpochConfig)(valid : ValidEpoch 𝓔)
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (𝓥      : VoteEvidence 𝓔 UID)
  where

 open ValidEpoch valid

 open import LibraBFT.Abstract.Records 𝓔 UID _≟UID_ 𝓥

 -- Here we use the bft-lemma provided by a ValidEpoch to prove convenient proprties relating honest
 -- peers to quorums and pairs of quorums.

 lemmaB1 : (q₁ : QC)(q₂ : QC) → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Meta-Honest-Member 𝓔 a)
 lemmaB1 q₁ q₂
   with bft-lemma {List-map vMember (qVotes q₁)}
                  {List-map vMember (qVotes q₂)}
                  (IsSorted-map⁻ vMember (qVotes q₁) (qVotes-C1 q₁))
                  (IsSorted-map⁻ vMember (qVotes q₂) (qVotes-C1 q₂))
                  (≤-trans (qVotes-C2 q₁)
                    (≡⇒≤ (sym (List-length-map vMember (qVotes q₁)))))
                  (≤-trans (qVotes-C2 q₂)
                    (≡⇒≤ (sym (List-length-map vMember (qVotes q₂)))))
 ...| α , (α∈v1 , α∈v2 , hα) = α , Any-map sym (Any-map⁻ α∈v1)
                                 , Any-map sym (Any-map⁻ α∈v2)
                                 , hα

 -- Any QC contains at least one honest verifier
 ∃Honest∈QC : (q : QC) → ∃[ α ] (Meta-Honest-Member 𝓔 α × α ∈QC q)
 ∃Honest∈QC q
   with IsSorted-map⁻ {_≤_ = _<Fin_} vMember (qVotes q) (qVotes-C1 q) |
        subst (EpochConfig.QSize 𝓔 ≤_) (sym (List-length-map vMember (qVotes q))) (qVotes-C2 q)
 ...| qsorted | qsize≤
   -- q contains an honest vote, find it using bft-lemma (use same QC twice)
   with bft-lemma qsorted qsorted qsize≤ qsize≤
 ...| α , α∈q , _α∈q' , honα = α , honα , Any-map sym (Any-map⁻ α∈q)
