{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Prelude

-- The ground types that are common across Abstract, Concrete and Impl
-- and some utility types
module LibraBFT.Base.Types where

  Epoch : Set
  Epoch = ℕ

  Round : Set
  Round = ℕ

  -- This was intended to be a simple way to flag meta-information without having it
  -- getting in the way.  It's important to ensure that an implementation does not
  -- use various information, such as who is honest.  However, we found this got in
  -- the way too much during development, so for now we get a similar effect by using
  -- a naming convention and enforcement via grep and eyeballs.  Maybe one day...
  Meta : ∀{ℓ} → Set ℓ → Set ℓ
  Meta x = x

  -- An EPRound is a 'compound round'; that is,
  -- is a round coupled with an epoch id.  As most of our
  -- proofs are per-epoch so far, these are not used, but
  -- they may be in future.
  EpRound : Set
  EpRound = Epoch × Round

  sucr : EpRound → EpRound
  sucr (e , r) = (e , suc r)

  epr-epoch : EpRound → Epoch
  epr-epoch = proj₁

  epr-round : EpRound → Round
  epr-round = proj₂

  epr₀ : EpRound
  epr₀ = (0 , 0)

  -- Compound rounds admit a total order
  data _<ER_ : EpRound → EpRound → Set where
    ince : ∀{e₀ e₁ r₀ r₁} → e₀ < e₁ → (e₀ , r₀) <ER (e₁ , r₁)
    incr : ∀{e r₀ r₁}     → r₀ < r₁ → (e  , r₀) <ER (e  , r₁)

  <ER-irrelevant : Irrelevant _<ER_
  <ER-irrelevant (ince x) (ince x₁) = cong ince (<-irrelevant x x₁)
  <ER-irrelevant (ince x) (incr x₁) = ⊥-elim (<-irrefl refl x)
  <ER-irrelevant (incr x) (ince x₁) = ⊥-elim (<-irrefl refl x₁)
  <ER-irrelevant (incr x) (incr x₁) = cong incr (<-irrelevant x x₁)

  <ER-asym : Asymmetric _<ER_
  <ER-asym (ince x) (ince x₁) = <-asym x x₁
  <ER-asym (ince x) (incr x₁) = <-irrefl refl x
  <ER-asym (incr x) (ince x₁) = <-irrefl refl x₁
  <ER-asym (incr x) (incr x₁) = <-asym x x₁

  <ER-trans : Transitive _<ER_
  <ER-trans (ince x) (ince x₁) = ince (<-trans x x₁)
  <ER-trans (ince x) (incr x₁) = ince x
  <ER-trans (incr x) (ince x₁) = ince x₁
  <ER-trans (incr x) (incr x₁) = incr (<-trans x x₁)

  <ER-irrefl : Irreflexive _≡_ _<ER_
  <ER-irrefl refl (ince x) = <-irrefl refl x
  <ER-irrefl refl (incr x) = <-irrefl refl x

  postulate -- prove, if needed/used
    <ER-cmp : Trichotomous _≡_ _<ER_
{- This <ER relation is not currently used. If it turns out to be
   used: TODO-1: finish this proof
    <ER-cmp (e₀ , r₀) (e₁ , r₁) with <-cmp e₀ e₁
    ...| tri≈ e₀≮e₁ refl e₁≮e₀ = {!!} {!!} {!!}
    ...| tri< e₀<e₁ e₀≢e₁ e₁≮e₀ = tri< (ince e₀<e₁) {!!} {!!}
    ...| tri> e₀≮e₁ e₀≢e₁ e₁<e₀ = {!!}

-}
  ep≮epr₀ : ∀{ep} → ¬ (ep <ER epr₀)
  ep≮epr₀ (ince ())
  ep≮epr₀ (incr ())

  _≤ER_ : EpRound → EpRound → Set
  er₀ ≤ER er₁ = er₀ ≡ er₁ ⊎ er₀ <ER er₁

  ≤ER⇒epoch≤ : ∀{er₀ er₁} → er₀ ≤ER er₁ → epr-epoch er₀ ≤ epr-epoch er₁
  ≤ER⇒epoch≤ (inj₁ refl) = ≤-refl
  ≤ER⇒epoch≤ (inj₂ (ince x)) = <⇒≤ x
  ≤ER⇒epoch≤ (inj₂ (incr x)) = ≤-refl

  ≤ER⇒round≤ : ∀{er₀ er₁} → er₀ ≤ER er₁ → epr-epoch er₀ ≡ epr-epoch er₁ → epr-round er₀ ≤ epr-round er₁
  ≤ER⇒round≤ (inj₁ refl) hyp1 = ≤-refl
  ≤ER⇒round≤ (inj₂ (ince x)) refl = ⊥-elim (<-irrefl refl x)
  ≤ER⇒round≤ (inj₂ (incr x)) hyp1 = <⇒≤ x

  ≤ER-intro : ∀{e₀ e₁ r₀ r₁} → e₀ ≤ e₁ → r₀ ≤ r₁ → (e₀ , r₀) ≤ER (e₁ , r₁)
  ≤ER-intro {e0} {e1} {r0} {r1} e r
    with e0 ≟ℕ e1
  ...| no le    = inj₂ (ince (≤∧≢⇒< e le))
  ...| yes refl
    with r0 ≟ℕ r1
  ...| no le    = inj₂ (incr (≤∧≢⇒< r le))
  ...| yes refl = inj₁ refl

  er≤0⇒er≡0 : ∀{er} → er ≤ER epr₀ → er ≡ epr₀
  er≤0⇒er≡0 (inj₁ x) = x
  er≤0⇒er≡0 (inj₂ (ince ()))
  er≤0⇒er≡0 (inj₂ (incr ()))

  <⇒≤ER : ∀{er₀ er₁} → er₀ <ER er₁ → er₀ ≤ER er₁
  <⇒≤ER = inj₂

  ≤ER-refl : Reflexive _≤ER_
  ≤ER-refl = inj₁ refl

  postulate  -- prove, if needed/used
    ≤ER-trans : Transitive _≤ER_
