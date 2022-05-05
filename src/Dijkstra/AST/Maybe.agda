{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Maybe where

open import Dijkstra.AST.Core
open import Haskell.Prelude using (_>>_; _>>=_; just; Maybe; nothing; return; Unit; unit; Void)
import      Level
open import Relation.Binary.PropositionalEquality

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

  bailWorks : ∀ {A} (a : A) i → ASTPredTrans.predTrans MaybePT (prog₁ a) BailWorks i
  bailWorks a unit maybeVoid maybeVoid≡nothing
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

MaybeSuf : ASTSufficientPT MaybeOpSem MaybePT
ASTSufficientPT.returnSuf MaybeSuf x P i wp = wp
ASTSufficientPT.bindSuf   MaybeSuf {A} {B} m f mSuf fSuf P unit wp
  with runMaybe m unit | inspect (runMaybe m) unit
... | nothing | [ eq ] = mSuf _ unit wp nothing (sym eq)
... | just y  | [ eq ] = let wp' = mSuf _ unit wp (just y) (sym eq)
                          in fSuf y P unit wp'
ASTSufficientPT.opSuf     MaybeSuf Maybe-bail f fSuf P i wp = wp

private
  bailWorksSuf : ∀ {A : Set} (a : A) i → (runMaybe (prog₁ a) i ≡ nothing)
--bailWorksSuf a i =
--  ASTSufficientPT.sufficient MaybeSuf (prog₁ a) BailWorks unit (bailWorks a unit)
  bailWorksSuf a i
    with runMaybe (prog₁ a) i
  ... | x≡x = refl

------------------------------------------------------------------------------

module Partiality where
  {- from "A predicate transformer semantics for effects"
     https://webspace.science.uu.nl/~swier004/publications/2019-icfp-submission-a.pdf
     https://zenodo.org/record/3257707#.Yec-nxPMJqt
  -}
  open Syntax
  open import Agda.Builtin.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat public using () renaming (ℕ to Nat; zero to Zero; suc to Succ)
  open import Data.Nat.DivMod
  open import Data.Product using (∃ ; ∃-syntax ; _×_)

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

  -- The proof of 'correct' in the Wouter paper uses wpPartial, which is like wp, but is for a
  -- Partial (Maybe) computation, and requires that the computation succeeds (i.e., returns a just)
  -- by making the post condition not hold when the computation returns nothing.  While not
  -- explicitly writing it as such, the following is the moral equivaelent, where PN plays the role
  -- of mustPT in the paper.
  PN : Expr → Post Nat
  PN e nothing  = ⊥
  PN e (just n) = e ⇓ n

  -- TUTORIAL: This example provides a good demonstration of how predTransMono can be used to
  -- construct proofs for ASTs that include ASTbind, and shows how Agda can figure out the required
  -- post condition from context, saving us from writing out ugly expressions for the continuation
  -- of a bind.  For example, we do not need to write out the second post condition in the type
  -- signature of PN⊆₁ below, because Agda figures it out from the goal.
  divWorks : ∀ (e : Expr) i → SafeDiv e → ASTPredTrans.predTrans MaybePT (⟦ e ⟧) (PN e) i
  divWorks (Val x₁) i x = ⇓Base
  divWorks (Div e₁ e₂) unit (¬e₂⇓0 , (sd₁ , sd₂)) =
    ASTPredTransMono.predTransMono MaybePTMono ⟦ e₁ ⟧ (PN e₁) _ PN⊆₁ unit ih₁
    where
    ih₁ = divWorks e₁ unit sd₁
    ih₂ = divWorks e₂ unit sd₂

    PN⊆₂ : ∀ n → e₁ ⇓ n →  PN e₂ ⊆ₒ _
    PN⊆₂ n pf₁ o () nothing refl
    PN⊆₂ n pf₁ .(just Zero) pf₂ (just Zero) refl = ¬e₂⇓0 pf₂
    PN⊆₂ n pf₁ .(just (Succ m)) pf₂ (just (Succ m)) refl =
      ⇓Step pf₁ pf₂

    PN⊆₁ : PN e₁ ⊆ₒ _
    PN⊆₁ o () nothing refl
    PN⊆₁ (just n) pf₁ .(just n) refl =
      ASTPredTransMono.predTransMono MaybePTMono ⟦ e₂ ⟧ (PN e₂) _ (PN⊆₂ n pf₁) unit ih₂
