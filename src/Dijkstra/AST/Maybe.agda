{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Maybe where

open import Dijkstra.AST.Core
open import Haskell.Prelude using (_>>_; _>>=_; just; Maybe; nothing; return; Unit; unit; Void)
open import Data.Product using (Σ)
import      Level
open import Relation.Binary.PropositionalEquality
open import Util.Prelude using (contradiction)

data MaybeCmd (C : Set) : Set₁ where
  Maybe-bail : MaybeCmd C

MaybeSubArg : {C : Set} (c : MaybeCmd C) → Set₁
MaybeSubArg Maybe-bail = Level.Lift _ Void

MaybeSubRet : {A : Set} {c : MaybeCmd A} (r : MaybeSubArg c) → Set
MaybeSubRet {c = Maybe-bail} ()

MaybeOps : ASTOps
ASTOps.Cmd    MaybeOps = MaybeCmd
ASTOps.SubArg MaybeOps = MaybeSubArg
ASTOps.SubRet MaybeOps = MaybeSubRet

MaybeD = AST MaybeOps

module Syntax where
  open import Dijkstra.AST.Syntax public

  bail : ∀ {A} → MaybeD A
  bail = ASTop Maybe-bail (λ ())

private

  prog₁ : ∀ {A} → A → MaybeD A
  prog₁ a =
    ASTbind (ASTop (Maybe-bail {Void}) (λ ()))
            (λ _ → ASTreturn  a)

  module prog₁ where
    open Syntax
    prog₁' : ∀ {A} → A → MaybeD A
    prog₁' a = do
      bail {Void}
      return a

MaybeTypes : ASTTypes
ASTTypes.Input  MaybeTypes   = Unit
ASTTypes.Output MaybeTypes A = Maybe A

open ASTTypes MaybeTypes

MaybeOpSem : ASTOpSem MaybeOps MaybeTypes
ASTOpSem.runAST MaybeOpSem (ASTreturn x) _ = just x
ASTOpSem.runAST MaybeOpSem (ASTbind m f) i
  with ASTOpSem.runAST MaybeOpSem m i
...| nothing = nothing
...| just x  = ASTOpSem.runAST MaybeOpSem (f x) i
ASTOpSem.runAST MaybeOpSem (ASTop Maybe-bail f) i = nothing

runMaybe = ASTOpSem.runAST MaybeOpSem

MaybebindPost : ∀ {A B} → (A → PredTrans B) → Post B → Post A
MaybebindPost _ P nothing  = P nothing
MaybebindPost f P (just y) = f y P unit

MaybebindPost⊆
  : ∀ {A B} (f : A → PredTrans B) (P₁ : Post B) (P₂ : Post A)
    → (P₁ nothing → P₂ nothing)
    → (∀ x → f x P₁ unit → P₂ (just x))
    → MaybebindPost f P₁ ⊆ₒ P₂
MaybebindPost⊆ f P₁ P₂ n⊆ j⊆ nothing wp = n⊆ wp
MaybebindPost⊆ f P₁ P₂ n⊆ j⊆ (just x) wp = j⊆ x wp

MaybePT : ASTPredTrans MaybeOps MaybeTypes
ASTPredTrans.returnPT MaybePT x P i               = P (just x)
-- Note that it is important *not* to pattern match the input as 'unit'.  Even though this is the
-- only constructor for Unit, Agda does not figure out that this case applies to a general Input
-- (because Input is of type Unit), and therefore does not expand this case when encountering
-- bindPT.
ASTPredTrans.bindPT   MaybePT f i Post x          = ∀ r → r ≡ x → MaybebindPost f Post r
ASTPredTrans.opPT     MaybePT Maybe-bail f Post i = Post nothing
-- This open is important because, without it, Agda does not know how to interpret bindPT and
-- therefore does not refine the goal sufficiently to enable the old λ ._ refl trick to get to the
-- MaybebindPost goal, for example.
open ASTPredTrans MaybePT

private
  BailWorks : ∀ {A} -> Post A
  BailWorks o = o ≡ nothing

  bailWorks  : ∀ {A} (a : A) i → ASTPredTrans.predTrans MaybePT (prog₁ a) BailWorks i
  bailWorks  a unit r         r≡nothing rewrite r≡nothing = refl

  -- "expanded" version for understanding
  bailWorks' : ∀ {A} (a : A) i → ASTPredTrans.predTrans MaybePT (prog₁ a) BailWorks i
  bailWorks' a unit maybeVoid maybeVoid≡nothing
                             -- MaybebindPost (λ x P i → P (just a)) BailWorks           maybeVoid
    with maybeVoid | maybeVoid≡nothing
  ... | n | n≡nothing        -- MaybebindPost (λ x P i → P (just a)) (λ o → o ≡ nothing) n
    rewrite n≡nothing        -- MaybebindPost (λ x P i → P (just a)) (λ o → o ≡ nothing) nothing
    = refl

MaybePTMono : ASTPredTransMono MaybePT
ASTPredTransMono.returnPTMono MaybePTMono x P₁ P₂ P₁⊆ₒP₂ i wp =
  P₁⊆ₒP₂ _ wp

ASTPredTransMono.bindPTMono₁  MaybePTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ nothing  wp .nothing  refl =
  P₁⊆ₒP₂ nothing (wp nothing refl)
ASTPredTransMono.bindPTMono₁  MaybePTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ (just y) wp .(just y) refl =
  monoF y P₁ P₂ P₁⊆ₒP₂ unit (wp (just y) refl)

ASTPredTransMono.bindPTMono₂  MaybePTMono {B1} {B2} f₁ f₂ f₁⊑f₂ unit P nothing wp .nothing refl =
  wp nothing refl
ASTPredTransMono.bindPTMono₂  MaybePTMono f₁ f₂ f₁⊑f₂ unit P (just y) wp .(just y) refl =
  f₁⊑f₂ y _ unit (wp (just y) refl)

ASTPredTransMono.opPTMono₁    MaybePTMono Maybe-bail f monoF P₁ P₂ P₁⊆ₒP₂ unit wp =
  P₁⊆ₒP₂ nothing wp
ASTPredTransMono.opPTMono₂    MaybePTMono Maybe-bail f₁ f₂ f₁⊑f₂ P i wp =
  wp

maybePTMono      = ASTPredTransMono.predTransMono MaybePTMono
maybePTMonoBind₂ = ASTPredTransMono.bindPTMono₂   MaybePTMono

MaybeSuf : ASTSufficientPT MaybeOpSem MaybePT
ASTSufficientPT.returnSuf MaybeSuf x P i wp = wp
ASTSufficientPT.bindSuf   MaybeSuf {A} {B} m f mSuf fSuf P unit wp
  with runMaybe m unit | inspect (runMaybe m) unit
... |  nothing         | [ eq ] = mSuf _ unit wp nothing (sym eq)
... |  just y          | [ eq ] = let wp' = mSuf _ unit wp (just y) (sym eq)
                                   in fSuf y P unit wp'
ASTSufficientPT.opSuf     MaybeSuf Maybe-bail f fSuf P i wp = wp

maybeSufficient = ASTSufficientPT.sufficient MaybeSuf

maybeSuffBind
  : ∀ {A B P} {Q : Post A} {i} (m : MaybeD A) (f : A → MaybeD B)
    → predTrans (m >>= f) P i
    → (P nothing → Q nothing)
    → (∀ x → predTrans (f x) P unit → Q (just x))
    → Q (runMaybe m i)
maybeSuffBind{P = P}{Q}{i} m f wp n⊆ j⊆ =
  MaybebindPost⊆ (λ x → predTrans (f x)) P Q n⊆ j⊆
    (runMaybe m i) (maybeSufficient m _ i wp _ refl)

private
  bailWorksSuf  : ∀ {A : Set} (a : A) i → (runMaybe (prog₁ a) i ≡ nothing)
  bailWorksSuf a i =
    ASTSufficientPT.sufficient MaybeSuf (prog₁ a) BailWorks unit (bailWorks a unit)

  -- alternate version
  bailWorksSuf' : ∀ {A : Set} (a : A) i → (runMaybe (prog₁ a) i ≡ nothing)
  bailWorksSuf' a i
    with runMaybe (prog₁ a) i
  ... | x≡x = refl

  postulate
    -- TODO-1 : prove postulated 'maybePTApp'
    -- TODO-1 : add comments comparing it to 'maybePTMono'
    maybePTApp
      : ∀ {A} {P₁ P₂ : Post A} (m : MaybeD A) i
        → predTrans m (λ o → P₁ o → P₂ o) i
        → predTrans m P₁ i
        → predTrans m P₂ i

------------------------------------------------------------------------------

module Partiality where

  {- Examples corresponding to
     "A predicate transformer semantics for effects"
     https://webspace.science.uu.nl/~swier004/publications/2019-icfp-submission-a.pdf
     https://zenodo.org/record/3257707#.Yec-nxPMJqt
  -}

  open Syntax
  open import Agda.Builtin.Unit using (⊤; tt)
  open import Data.Empty        using (⊥; ⊥-elim)
  open import Data.Nat          public renaming (ℕ to Nat; zero to Zero; suc to Succ)
  open import Data.Nat.DivMod
  open import Data.Product      using (∃ ; ∃-syntax ; _×_)
  open import Function.Base     using (case_of_)
  open import Util.Prelude      using (absurd_case_of_)

  Partial : {A : Set} → (P : A → Set) → Maybe A → Set
  Partial _ nothing  = ⊥
  Partial P (just x) = P x

  data Expr : Set where
    Val : Nat  -> Expr
    Div : Expr -> Expr -> Expr

  data _⇓_ : Expr -> Nat -> Set where
    ⇓Base : forall {n}
         -> Val n ⇓ n
    ⇓Step : forall {el er n1 n2}
         ->     el    ⇓  n1
         ->        er ⇓         (Succ n2) -- divisor is non-zero
         -> Div el er ⇓ (n1 div (Succ n2))

  _÷_ : Nat -> Nat -> MaybeD Nat
  n ÷ Zero     = bail
  n ÷ (Succ k) = ASTreturn (n div (Succ k))

  -- ⟦_⟧ : Expr -> MaybeD Nat
  -- ⟦ Val x ⟧     = return x
  -- ⟦ Div e1 e2 ⟧ = ⟦ e1 ⟧ >>= \v1 ->
  --                 ⟦ e2 ⟧ >>= \v2 ->
  --                 v1 ÷ v2

  ⟦_⟧ : Expr -> MaybeD Nat
  ⟦ Val x ⟧     = ASTreturn x
  ⟦ Div e1 e2 ⟧ = ASTbind (⟦ e1 ⟧) (\v1 ->
                  ASTbind (⟦ e2 ⟧) (\v2 ->
                   (v1 ÷ v2)))

  wpPartial
    : {A : Set} {B : A → Set} (f : (x : A) → MaybeD (B x))
      (P : (x : A) → B x → Set) → A → Set
  wpPartial f P x =
    predTrans (f x) (Partial (P x)) unit

  record Pair {l l'} (a : Set l) (b : Set l') : Set (l Level.⊔ l') where
    constructor _,_
    field
      fst : a
      snd : b

  _∧_ : ∀ {l l'} -> Set l -> Set l' -> Set (l Level.⊔ l')
  _∧_ A B = Pair A B
  infixr 1 _∧_

  SafeDiv : Expr -> Set
  SafeDiv (Val x)     = ⊤
  SafeDiv (Div el er) = (er ⇓ Zero -> ⊥) ∧ SafeDiv el ∧ SafeDiv er

  ------------------------------------------------------------------------------
  -- everything above from Wouter paper (modified with our AST)
  -- everything below our attempts to prove sufficient, sound, complete, ...

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
  correct : ∀ (e : Expr) i → SafeDiv e → ASTPredTrans.predTrans MaybePT (⟦ e ⟧) (PN e) i
  correct (Val _)        _                   _   = ⇓Base
  correct (Div e₁ e₂) unit (¬e₂⇓0 , (sd₁ , sd₂)) =
    ASTPredTransMono.predTransMono MaybePTMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
   where
    ih₁ = correct e₁ unit sd₁
    ih₂ = correct e₂ unit sd₂

    PN⊆₂ : ∀ n → e₁ ⇓ n → PN e₂ ⊆ₒ _
    PN⊆₂ _    _              _        ()  nothing        refl
    PN⊆₂ _    _ .(just       _)  e₂⇓Zero (just Zero)     refl = ¬e₂⇓0 e₂⇓Zero
    PN⊆₂ _ e₁⇓n .(just (Succ _)) e₂⇓Succ (just (Succ _)) refl = ⇓Step e₁⇓n e₂⇓Succ

    PN⊆₁ : PN e₁ ⊆ₒ _
    PN⊆₁       _    ()   nothing refl
    PN⊆₁ (just n) e₁⇓n .(just n) refl =
      ASTPredTransMono.predTransMono MaybePTMono ⟦ e₂ ⟧ (PN e₂) _ (PN⊆₂ n e₁⇓n) unit ih₂

  Dom : {A : Set} {B : A → Set}
        → ((x : A) → MaybeD (B x)) → A → Set
  Dom f = wpPartial f λ _ _ → ⊤

  DomDiv : ∀ {e₁ e₂}
           → Dom ⟦_⟧ (Div e₁ e₂)
           → Dom ⟦_⟧ e₁
             ∧ wpPartial ⟦_⟧ (λ _ → _> 0) e₂
  Pair.fst (DomDiv{e₁}{e₂} dom) =
    maybePTMono ⟦ e₁ ⟧ _ _ ⊆Partial unit dom
    where
    ⊆Partial : _ ⊆ₒ Partial (λ _ → ⊤)
    ⊆Partial nothing wp = wp _ refl
    ⊆Partial (just m) wp = tt
  Pair.snd (DomDiv{e₁}{e₂} dom) =
    maybeSuffBind {Q = λ _ → _} ⟦ e₁ ⟧
      (λ m → ⟦ e₂ ⟧ >>= λ n → m ÷ n) dom (λ ())
      λ m wp →
        maybePTMono ⟦ e₂ ⟧ _ _ (⊆Partial m) unit wp
      where
      ⊆Partial : ∀ m → _ ⊆ₒ Partial (_> 0)
      ⊆Partial m nothing wp = wp _ refl
      ⊆Partial m (just Zero) wp = ⊥-elim (wp _ refl)
      ⊆Partial m (just (Succ n)) wp = s≤s z≤n

  sound : ∀ (e : Expr) i → Dom ⟦_⟧ e → predTrans ⟦ e ⟧ (PN e) i
  sound (Val x) unit dom = ⇓Base
  sound (Div e₁ e₂) unit dom =
    maybePTMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
    where
    ih₁ = sound e₁ unit (Pair.fst (DomDiv{e₁}{e₂} dom))
    ih₂ =
      sound e₂ unit
        (maybePTMono ⟦ e₂ ⟧ _ _ (λ { nothing () ; (just x) _ → tt}) unit
          (Pair.snd (DomDiv{e₁}{e₂} dom)))

    PN⊆₂ : ∀ n → e₁ ⇓ n → Partial (λ n → e₂ ⇓ n ∧ (n > 0)) ⊆ₒ _
    PN⊆₂ n e₁⇓n (just (Succ x)) wp .(just (Succ x)) refl =
      ⇓Step e₁⇓n (Pair.fst wp)

    PN⊆₁ : PN e₁ ⊆ₒ _
    PN⊆₁ (just m) e₁⇓m ._ refl =
      maybePTMono ⟦ e₂ ⟧ _ _ (PN⊆₂ m e₁⇓m) unit
        (maybePTApp ⟦ e₂ ⟧ unit
          (maybePTMono ⟦ e₂ ⟧ _ _
            (λ where
              (just x) wp₁ wp₂ → wp₂ , wp₁)
            unit ((Pair.snd (DomDiv{e₁}{e₂} dom))))
          ih₂)

  -------------------------
  -- alternate proof of sound

  deterministic : ∀ {e n₁ n₂} → e ⇓ n₁ → e ⇓ n₂ → n₁ ≡ n₂
  deterministic ⇓Base ⇓Base = refl
  deterministic (⇓Step e⇓n₁ e⇓n₂) (⇓Step e⇓n₃ e⇓n₄)
    with deterministic e⇓n₁ e⇓n₃
    |    deterministic e⇓n₂ e⇓n₄
  ... | refl | refl = refl

  dom' : (Expr -> MaybeD Nat)
      -> Expr
      -> Set
  dom' f e =
    case runMaybe (f e) unit of λ where
      nothing  -> ⊥
      (just _) -> ⊤

  Dom' : (Expr -> MaybeD Nat) -> Expr -> Set
  Dom' f a@(Val _)     =  dom' f a
  Dom' f a@(Div el er) = (dom' f a) ∧ Dom' f el ∧ Dom' f er

  sound' : ∀ (e : Expr) i → Dom' ⟦_⟧ e → ASTPredTrans.predTrans MaybePT (⟦ e ⟧) (PN e) i
  sound' (Val _)        _                  _   = ⇓Base
  sound' (Div e₁ e₂) unit (ddiv , (de₁ , de₂)) =
    ASTPredTransMono.predTransMono MaybePTMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
   where
    ih₁ = sound' e₁ unit de₁
    ih₂ = sound' e₂ unit de₂

    PN⊆₂ : ∀ n → e₁ ⇓ n → PN e₂ ⊆ₒ _
    PN⊆₂ _ e₁⇓n (just (Succ _)) e₂⇓Succ .(just (Succ _)) refl = ⇓Step e₁⇓n e₂⇓Succ
    PN⊆₂ _ e₁⇓n (just       0)  e₂⇓0     (just       0)  refl
      with   runMaybe ⟦ e₁ ⟧ unit
           | runMaybe ⟦ e₂ ⟧ unit | inspect (runMaybe ⟦ e₂ ⟧) unit
           | ASTSufficientPT.sufficient MaybeSuf ⟦ e₂ ⟧ _ unit ih₂
    ... | just _ | nothing       | [ eq₂ ] |       _ rewrite eq₂ = ⊥-elim ddiv
    ... | just _ | just 0        | [ eq₂ ] |       _ rewrite eq₂ = ⊥-elim ddiv
    ... | just l | just (Succ _) | [ eq₂ ] | e₂⇓Succ             =
      absurd (Succ _ ≡ 0) case (deterministic e₂⇓Succ e₂⇓0) of λ ()

    PN⊆₁ : PN e₁ ⊆ₒ _
    PN⊆₁ (just n) e₁⇓n .(just n) refl =
      ASTPredTransMono.predTransMono MaybePTMono ⟦ e₂ ⟧ (PN e₂) _ (PN⊆₂ n e₁⇓n) unit ih₂
