{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Dijkstra.AST.Prelude
open import Data.Nat          renaming (ℕ to Nat; zero to Zero; suc to Succ)
open import Data.Nat.DivMod

module Dijkstra.AST.Examples.Maybe.Partiality where
open import Dijkstra.AST.Maybe

{- Examples corresponding to
   "A predicate transformer semantics for effects"
   https://webspace.science.uu.nl/~swier004/publications/2019-icfp-submission-a.pdf
   https://zenodo.org/record/3257707#.Yec-nxPMJqt
-}

Partial : {A : Set} → (P : A → Set) → Maybe A → Set
Partial _ nothing  = ⊥
Partial P (just x) = P x

data Expr : Set where
  Val : Nat  → Expr
  Div : Expr → Expr → Expr

-- big step evaluator
data _⇓_ : Expr → Nat → Set where
  ⇓Base : forall {n}
       → Val n ⇓ n
  ⇓Step : forall {el er n1 n2}
       →     el    ⇓       n1
       →        er ⇓          (Succ n2) -- divisor is non-zero
       → Div el er ⇓ _div_ n1 (Succ n2)

module _ where
  _ : Set
  _ = Partial (Val 1 ⇓_) (just 1)
  _ : Partial (Val 1 ⇓_) (just 1)
  _ = ⇓Base
  _ : Set
  _ = Partial (Val 1 ⇓_) nothing
  {- cannot be constructed
  _ : Partial (Val 1 ⇓_) nothing
  _ = {!!}
  -}

_÷_ : Nat → Nat → MaybeAST Nat
n ÷  Zero    = bail
n ÷ (Succ k) = return (n div (Succ k))

⟦_⟧ : Expr → MaybeAST Nat
⟦ Val x     ⟧ = return x
⟦ Div e1 e2 ⟧ = ⟦ e1 ⟧ >>= \v1 →
                ⟦ e2 ⟧ >>= \v2 →
                v1 ÷ v2

module _ where
  open import Dijkstra.AST.Core

  -- Equivalent evaluator expressed using the Core AST defintion.
  ⟦_⟧' : Expr → MaybeAST Nat
  ⟦ Val x     ⟧' = ASTreturn x
  ⟦ Div e1 e2 ⟧' = ASTbind (⟦ e1 ⟧') (\v1 →
                   ASTbind (⟦ e2 ⟧') (\v2 →
                    (v1 ÷ v2)))

wpPartial
  : {A : Set} → {B : A → Set}
 → ((x : A)  → MaybeAST (B x))
 → ((x : A)  →           B x → Set)
 → (     A   →                  Set)
wpPartial a→partialBa a→ba→Set a =
  predTrans (a→partialBa a) (Partial (a→ba→Set a)) unit

module _ where
  _ : Expr → Set
  _ = wpPartial ⟦_⟧ _⇓_
  _ : wpPartial ⟦_⟧ _⇓_ ≡ λ expr → predTrans (⟦_⟧ expr) (Partial (_⇓_ expr)) unit
  _ = refl

  _ : wpPartial ⟦_⟧ _⇓_ (Val 1)
  _ = ⇓Base

  _ : Set
  _ = wpPartial ⟦_⟧ _⇓_ (Div (Val 1) (Val 1))
  x : wpPartial ⟦_⟧ _⇓_ (Div (Val 1) (Val 1))
  x (just 1) _eql (just 1) _eqr = ⇓Step ⇓Base ⇓Base

  _ : Set
  _ = wpPartial ⟦_⟧ _⇓_ (Div (Val 1) (Val 0))
  {- this type cannot be constructed
  _ : wpPartial ⟦_⟧ _⇓_ (Div (Val 1) (Val 0))
  _ = {!!}
  -}

record Pair {l l'} (a : Set l) (b : Set l') : Set (l ℓ⊔ l') where
  constructor _,_
  field
    fst : a
    snd : b

_∧_ : ∀ {l l'} → Set l → Set l' → Set (l ℓ⊔ l')
_∧_ A B = Pair A B
infixr 1 _∧_

SafeDiv : Expr → Set
SafeDiv (Val x)     = ⊤
SafeDiv (Div el er) = (er ⇓ Zero → ⊥) ∧ SafeDiv el ∧ SafeDiv er

------------------------------------------------------------------------------
-- Everything above from Wouter paper (modified with our AST).
-- Everything below is proving sufficient, sound, complete, ..., using our framework.

-- The proof of 'correct' in the Wouter paper uses wpPartial.
-- wpPartial is like wp, but it is for a Partial (Maybe) computation
-- - it requires the computation to succeed (i.e., returns a just)
--   by making the post condition not hold when the computation returns nothing.
-- PN is the functional equivalent, where PN plays the role of mustPT in the paper.
PN : Expr → Post Nat
PN e = Partial (e ⇓_)

-- TUTORIAL:
-- Demonstrates how predTransMono can be used
-- - to construct proofs for ASTs that include ASTbind, and
-- - shows how Agda can figure out the required post condition from context,
--   saving the need to write (ugly) expressions for the continuation of a bind.
--   - e.g., The underscore in the type signature of PN⊆₁ below (the second post condition)
--           because Agda figures it out from the goal.
-- TODO-1: show steps needed in order to get Agda to infer types indicated by '_'
--         in the type signatures of PN⊆₁ and PN⊆₂
correct : ∀ (e : Expr) i → SafeDiv e → predTrans (⟦ e ⟧) (PN e) i
correct (Val _)        _                   _   = ⇓Base
correct (Div e₁ e₂) unit (¬e₂⇓0 , (sd₁ , sd₂)) =
  predTransMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
 where
  ih₁ = correct e₁ unit sd₁
  ih₂ = correct e₂ unit sd₂

  PN⊆₂ : ∀ n → e₁ ⇓ n → PN e₂ ⊆ₒ _
  PN⊆₂ _    _              _        ()  nothing        refl
  PN⊆₂ _    _ .(just       _)  e₂⇓Zero (just  Zero)    refl = ¬e₂⇓0 e₂⇓Zero
  PN⊆₂ _ e₁⇓n .(just (Succ _)) e₂⇓Succ (just (Succ _)) refl = ⇓Step e₁⇓n e₂⇓Succ

  PN⊆₁ : PN e₁ ⊆ₒ _
  PN⊆₁       _    ()   nothing refl
  PN⊆₁ (just n) e₁⇓n .(just n) refl =
    predTransMono ⟦ e₂ ⟧ (PN e₂) _ (PN⊆₂ n e₁⇓n) unit ih₂

module _ where
  _ :          Val 3 ⇓ 3
  _ = correct (Val 3) unit tt

  {- TODO
  _ :         {!!} -- Div (Val 3) (Val 1) ⇓ 3
  _ = correct (Div (Val 3) (Val 1)) unit ((λ ()) , (tt , tt))
  -}

dom : {A : Set} → {B : A → Set}
   → ((x : A) → MaybeAST (B x))
   → (A → Set)
dom f = wpPartial f λ _ _ → ⊤

DomDiv : ∀ {e₁ e₂}
      → dom ⟦_⟧ (Div e₁ e₂)
      → dom ⟦_⟧ e₁ ∧ wpPartial ⟦_⟧ (λ _ → _> 0) e₂
Pair.fst (DomDiv {e₁} dom) =
  predTransMono ⟦ e₁ ⟧ _ _ ⊆Partial unit dom
 where
  ⊆Partial : _ ⊆ₒ Partial (λ _ → ⊤)
  ⊆Partial nothing  wp = wp _ refl
  ⊆Partial (just m) wp = tt
Pair.snd (DomDiv {e₁} {e₂} dom) =
  maybeSuffBind {Q = λ _ → _}
    ⟦ e₁ ⟧
    (λ m → ⟦ e₂ ⟧ >>= λ n → m ÷ n)
    dom
    (λ ())
    λ m wp → predTransMono ⟦ e₂ ⟧ _ _ (⊆Partial m) unit wp
   where
    ⊆Partial : ∀ m → _ ⊆ₒ Partial (_> 0)
    ⊆Partial _  nothing        wp = wp _ refl
    ⊆Partial _ (just  Zero)    wp = ⊥-elim (wp _ refl)
    ⊆Partial _ (just (Succ _))  _ = s≤s z≤n

sound : ∀ (e : Expr) i → dom ⟦_⟧ e → predTrans ⟦ e ⟧ (PN e) i
sound (Val x)     unit dom = ⇓Base
sound (Div e₁ e₂) unit dom =
  predTransMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
 where
  ih₁ = sound e₁ unit (Pair.fst (DomDiv {e₁} {e₂} dom))
  ih₂ = sound e₂ unit
          (predTransMono ⟦ e₂ ⟧ _ _ (λ { nothing () ; (just _) _ → tt}) unit
            (Pair.snd (DomDiv {e₁} {e₂} dom)))

  PN⊆₂ : ∀ n → e₁ ⇓ n → Partial (λ n → e₂ ⇓ n ∧ (n > 0)) ⊆ₒ _
  PN⊆₂ _ e₁⇓n (just (Succ x)) wp .(just (Succ x)) refl =
    ⇓Step e₁⇓n (Pair.fst wp)

  PN⊆₁ : PN e₁ ⊆ₒ _
  PN⊆₁ (just m) e₁⇓m ._ refl =
    predTransMono ⟦ e₂ ⟧ _ _ (PN⊆₂ m e₁⇓m) unit
      (maybePTApp ⟦ e₂ ⟧ unit
        (predTransMono ⟦ e₂ ⟧ _ _
          (λ where
            (just x) wp₁ wp₂ → wp₂ , wp₁)
          unit ((Pair.snd (DomDiv {e₁} {e₂} dom))))
        ih₂)

-------------------------
-- alternate proof of sound

deterministic : ∀ {e n₁ n₂} → e ⇓ n₁ → e ⇓ n₂ → n₁ ≡ n₂
deterministic  ⇓Base             ⇓Base = refl
deterministic (⇓Step e⇓n₁ e⇓n₂) (⇓Step e⇓n₃ e⇓n₄)
  with deterministic e⇓n₁ e⇓n₃
  |    deterministic e⇓n₂ e⇓n₄
... | refl | refl = refl

dom' : (Expr → MaybeAST Nat)
    → Expr
    → Set
dom' f e =
  case runMaybeAST (f e) unit of λ where
    nothing  → ⊥
    (just _) → ⊤

Dom' : (Expr → MaybeAST Nat) → Expr → Set
Dom' f a@(Val _)     =  dom' f a
Dom' f a@(Div el er) = (dom' f a) ∧ Dom' f el ∧ Dom' f er

sound' : ∀ (e : Expr) i → Dom' ⟦_⟧ e → predTrans (⟦ e ⟧) (PN e) i
sound' (Val _)        _                  _   = ⇓Base
sound' (Div e₁ e₂) unit (ddiv , (de₁ , de₂)) =
  predTransMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
 where
  ih₁ = sound' e₁ unit de₁
  ih₂ = sound' e₂ unit de₂

  PN⊆₂ : ∀ n → e₁ ⇓ n → PN e₂ ⊆ₒ _
  PN⊆₂ _ e₁⇓n (just (Succ _)) e₂⇓Succ .(just (Succ _)) refl = ⇓Step e₁⇓n e₂⇓Succ
  PN⊆₂ _ e₁⇓n (just       0)  e₂⇓0     (just       0)  refl
    with            runMaybeAST ⟦ e₁ ⟧   unit
         |          runMaybeAST ⟦ e₂ ⟧   unit
         | inspect (runMaybeAST ⟦ e₂ ⟧)  unit
         |          sufficient  ⟦ e₂ ⟧ _ unit ih₂
  ... | just _ | nothing       | [ eq₂ ] |       _ rewrite eq₂ = ⊥-elim ddiv
  ... | just _ | just 0        | [ eq₂ ] |       _ rewrite eq₂ = ⊥-elim ddiv
  ... | just _ | just (Succ _) |      _  | e₂⇓Succ             =
    absurd (Succ _ ≡ 0) case (deterministic e₂⇓Succ e₂⇓0) of λ ()

  PN⊆₁ : PN e₁ ⊆ₒ _
  PN⊆₁ (just n) e₁⇓n .(just n) refl =
    predTransMono  ⟦ e₂ ⟧ (PN e₂) _ (PN⊆₂ n e₁⇓n) unit ih₂

