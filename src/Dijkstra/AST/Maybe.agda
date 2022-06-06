{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Maybe where

open import Dijkstra.AST.Branching
open import Dijkstra.AST.Core
open import Haskell.Prelude using (_>>_; _>>=_; just; Maybe; nothing; return; Unit; unit; Monad; Void)
open import Data.Product using (Σ)
import      Level
open import Relation.Binary.PropositionalEquality
open import Util.Prelude using (contradiction; id; Left)
open        ASTExtension

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

MaybeAST = AST MaybeOps

module Syntax where
  open import Dijkstra.AST.Syntax public

  bail : ∀ {A} → MaybeAST A
  bail = ASTop Maybe-bail (λ ())

private

  prog₁ : ∀ {A} → A → MaybeAST A
  prog₁ a =
    ASTbind (ASTop (Maybe-bail {Void}) (λ ()))
            (λ _ → ASTreturn  a)

  module prog₁ where
    open Syntax
    prog₁' : ∀ {A} → A → MaybeAST A
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

runMaybeAST = ASTOpSem.runAST MaybeOpSem

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
  bailWorks  a unit r refl = refl

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
  with runMaybeAST m unit | inspect (runMaybeAST m) unit
... |  nothing            | [ eq ] = mSuf _ unit wp nothing (sym eq)
... |  just y             | [ eq ] = let wp' = mSuf _ unit wp (just y) (sym eq)
                                      in fSuf y P unit wp'
ASTSufficientPT.opSuf     MaybeSuf Maybe-bail f fSuf P i wp = wp

maybeSufficient = ASTSufficientPT.sufficient MaybeSuf

maybeSuffBind
  : ∀ {A B P} {Q : Post A} {i} (m : MaybeAST A) (f : A → MaybeAST B)
    → predTrans (m >>= f) P i
    → (P nothing → Q nothing)
    → (∀ x → predTrans (f x) P unit → Q (just x))
    → Q (runMaybeAST m i)
maybeSuffBind{P = P}{Q}{i} m f wp n⊆ j⊆ =
  MaybebindPost⊆ (λ x → predTrans (f x)) P Q n⊆ j⊆
    (runMaybeAST m i) (maybeSufficient m _ i wp _ refl)

-- This property says that predTrans really is the *weakest* precondition for a
-- postcondition to hold after running a MaybeAST.
Post⇒wp : ∀ {A} → MaybeAST A → Input → Set₁
Post⇒wp {A} m i =
  (P : Post A)
  → P (runMaybeAST m i)
  → predTrans m P i

predTrans-is-weakest : ∀ {A} → (m : MaybeAST A) → Post⇒wp {A} m unit
predTrans-is-weakest (ASTreturn _) _ = id
predTrans-is-weakest (ASTbind m f) _ Pr
   with predTrans-is-weakest m
...| rec
  with runMaybeAST m unit
... | nothing = rec _ λ where _ refl → Pr
... | just x  = rec _ λ where r refl → predTrans-is-weakest (f x) _ Pr
predTrans-is-weakest (ASTop Maybe-bail f) P = id

maybePTApp
    : ∀ {A} {P₁ P₂ : Post A} (m : MaybeAST A) i
      → predTrans m (λ o → P₁ o → P₂ o) i
      → predTrans m P₁ i
      → predTrans m P₂ i
maybePTApp {_} {P₁} {P₂} m unit imp pt1 =
  predTrans-is-weakest m P₂
    (ASTSufficientPT.sufficient MaybeSuf m (λ o → P₁ o → P₂ o) unit imp
      (ASTSufficientPT.sufficient MaybeSuf m P₁ unit pt1))

MaybeExtOps    = BranchOps MaybeOps
MaybeASTExt    = AST MaybeExtOps
MaybePTExt     = PredTransExtension.BranchPT MaybePT
runMaybeASTExt = ASTOpSem.runAST (OpSemExtension.BranchOpSem MaybeOpSem)
MaybePTMonoExt = PredTransExtensionMono.BranchPTMono MaybePTMono
MaybeSufExt    = SufficientExtension.BranchSuf MaybePTMono MaybeSuf

module MaybeBranchingSyntax where

  bail : ∀ {A} → AST MaybeExtOps A
  bail =  ASTop (Left Maybe-bail) λ ()

  instance
    Monad-Maybe-AST : Monad (AST MaybeExtOps)
    Monad.return Monad-Maybe-AST = ASTreturn
    Monad._>>=_  Monad-Maybe-AST = ASTbind

private
  -- an easy example using sufficient
  bailWorksSuf  : ∀ {A : Set} (a : A) i → (runMaybeAST (prog₁ a) i ≡ nothing)
  bailWorksSuf a i =
    ASTSufficientPT.sufficient MaybeSuf (prog₁ a) BailWorks unit (bailWorks a unit)

  -- alternate version, showing that it's trivial in this case
  bailWorksSuf' : ∀ {A : Set} (a : A) i → (runMaybeAST (prog₁ a) i ≡ nothing)
  bailWorksSuf' a i = refl

