{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- As we are interested in using Either for error handling (and providing the Either-bail command
-- for this purpose), we call the Left type "Err"
module Dijkstra.AST.Either (Err : Set) where

open import Data.Empty
open import Data.Product using (_×_) -- ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Dijkstra.AST.Core
open import Dijkstra.AST.Branching
open import Dijkstra.Syntax
open import Haskell.Prelude hiding (return)
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality
open        ASTExtension

data EitherCmd (A : Set) : Set₁ where
  Either-bail : Err → EitherCmd A

EitherSubArg : {A : Set} (a : EitherCmd A) → Set₁
EitherSubArg (Either-bail _) = Level.Lift _ Void

EitherSubRet : {A : Set} {c : EitherCmd A} (r : EitherSubArg c) → Set
EitherSubRet {c = Either-bail _} _ = Void

EitherOps : ASTOps
ASTOps.Cmd    EitherOps  = EitherCmd
ASTOps.SubArg EitherOps  = EitherSubArg
ASTOps.SubRet EitherOps  = EitherSubRet

EitherAST = AST EitherOps

module Syntax where
  open import Dijkstra.AST.Syntax public
  open import Dijkstra.Syntax

  bail : ∀ {A} → Err → EitherAST A
  bail a = ASTop (Either-bail a) λ ()

  return : ∀ {A} → A → EitherAST A
  return a = ASTreturn a

private
  prog₁ : ∀ {A} → Err → A → EitherAST A
  prog₁ e a =
    -- Either-bail always returns left, so Agda cannot infer the
    -- type that it would return if it were to return Right, so
    -- we provide a type explicitly (Unit, in this case)
    ASTbind (ASTop (Either-bail {Unit} e) λ ()) λ _ →
      ASTreturn a

  module prog₁ where
    open Syntax
    prog₁' : ∀ {A} → Err → A → EitherAST A
    prog₁' {A} e a = do
      bail {Void} e
      return a

EitherTypes : ASTTypes
ASTTypes.Input  EitherTypes   = Unit -- We can always run an Either program.  In contrast, for an
                                     -- RWS program, we need environment and prestate (Ev and St,
                                     -- respectively)
ASTTypes.Output EitherTypes A = Either Err A
open ASTTypes EitherTypes

EitherOpSem : ASTOpSem EitherOps EitherTypes
ASTOpSem.runAST EitherOpSem (ASTreturn x) _ = Right x
ASTOpSem.runAST EitherOpSem (ASTbind m f) i
  with ASTOpSem.runAST EitherOpSem m i
...| Left a = Left a
...| Right x = ASTOpSem.runAST EitherOpSem (f x) i
ASTOpSem.runAST EitherOpSem (ASTop (Either-bail a) f) i = Left a

runEither = ASTOpSem.runAST EitherOpSem

EitherbindPost : ∀ {A B} → (A → PredTrans B) → Post B → Post A
EitherbindPost _ P (Left x)  = P (Left x)
EitherbindPost f P (Right y) = f y P unit

EitherPT : ASTPredTrans EitherOps EitherTypes
ASTPredTrans.returnPT EitherPT x P i = P (Right x)
ASTPredTrans.bindPT EitherPT {A} {B} f i Post x =
  ∀ r → r ≡ x → EitherbindPost f Post r
ASTPredTrans.opPT EitherPT (Either-bail a) f Post i = Post (Left a)
open ASTPredTrans EitherPT

private
  -- If Either-bail did not work (e.g., if it were a noop), prog₁ would return Right a and the proof
  -- would fail
  BailWorks : ∀ {A : Set} → Err → Post A
  BailWorks e = _≡ Left e

  bailWorks : ∀ e i {A : Set} → (a : A) → ASTPredTrans.predTrans EitherPT (prog₁ e a) (BailWorks e) i
  bailWorks e unit _ _ refl = refl

EitherPTMono : ASTPredTransMono EitherPT
ASTPredTransMono.returnPTMono EitherPTMono x P₁ P₂ P₁⊆ₒP₂ i wp =
   P₁⊆ₒP₂ _ wp

ASTPredTransMono.bindPTMono₁ EitherPTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ (Left x ) wp .(Left x ) refl =
  P₁⊆ₒP₂ (Left x) (wp (Left x) refl)
ASTPredTransMono.bindPTMono₁ EitherPTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ (Right y) wp .(Right y) refl =
  monoF y P₁ P₂ P₁⊆ₒP₂ unit (wp (Right y) refl)

ASTPredTransMono.bindPTMono₂ EitherPTMono {B1} {B2} f₁ f₂ f₁⊑f₂ unit P (Left x)  wp .(Left x) refl =
  wp (Left x) refl
ASTPredTransMono.bindPTMono₂ EitherPTMono f₁ f₂ f₁⊑f₂ unit P (Right y) wp .(Right y) refl =
  f₁⊑f₂ y _ unit (wp (Right y) refl)

ASTPredTransMono.opPTMono₁ EitherPTMono (Either-bail x) f monoF P₁ P₂ P₁⊆ₒP₂ unit wp =
  P₁⊆ₒP₂ (Left x) wp

ASTPredTransMono.opPTMono₂ EitherPTMono (Either-bail x) f₁ f₂ f₁⊑f₂ P i wp =
  wp

EitherSuf : ASTSufficientPT EitherOpSem EitherPT
ASTSufficientPT.returnSuf EitherSuf x P i wp = wp
ASTSufficientPT.bindSuf EitherSuf {A} {B} m f mSuf fSuf P unit wp
   with  ASTOpSem.runAST EitherOpSem m  unit  | inspect
        (ASTOpSem.runAST EitherOpSem m) unit
... | Left  x | [ R ] = mSuf _ unit wp (Left x) (sym R)
... | Right y | [ R ] = let wp' = mSuf _ unit wp (Right y) (sym R)
                         in fSuf y P unit wp'
ASTSufficientPT.opSuf EitherSuf (Either-bail x) f fSuf P i wp = wp

-- This property says that predTrans really is the *weakest* precondition for a
-- postcondition to hold after running a MaybeD.
Post⇒wp : ∀ {A} → EitherAST A → Input → Set₁
Post⇒wp {A} e i =
  (P : Post A)
  → P (runEither e i)
  → predTrans e P i

predTrans-is-weakest : ∀ {A} → (e : EitherAST A) → Post⇒wp {A} e unit
predTrans-is-weakest (ASTreturn _) _ = id
predTrans-is-weakest (ASTbind e f) _ Pr
   with predTrans-is-weakest e
...| rec
  with runEither e unit
... | Left  _ = rec _ λ where _ refl →                              Pr
... | Right r = rec _ λ where _ refl → predTrans-is-weakest (f r) _ Pr
predTrans-is-weakest (ASTop (Either-bail _) _) _ = id

private
  bailWorksSuf : ∀ e {A : Set} (a : A) i → (runEither (prog₁ e a) i ≡ Left e)
  bailWorksSuf e a i = ASTSufficientPT.sufficient EitherSuf (prog₁ e a) (BailWorks e) unit (bailWorks e unit a )

EitherExtOps    = BranchOps EitherOps
EitherDExt      = AST EitherExtOps
EitherPTExt     = PredTransExtension.BranchPT EitherPT
runEitherExt    = ASTOpSem.runAST (OpSemExtension.BranchOpSem EitherOpSem)
EitherPTMonoExt = PredTransExtensionMono.BranchPTMono EitherPTMono
EitherSufExt    = SufficientExtension.BranchSuf EitherPTMono EitherSuf

module SyntaxExt where
  open import Dijkstra.AST.Syntax public
  open import Dijkstra.Syntax

  EitherD-maybe : ∀ {A B : Set} → EitherDExt B → (A → EitherDExt B) → Maybe A → EitherDExt B
  EitherD-maybe m f mb = ASTop (Right (BCmaybe mb))
                               λ { (Level.lift nothing)  → m
                                 ; (Level.lift (just j)) → f j
                                 }
  instance
    Monad-EitherDAST : Monad EitherDExt
    Monad.return Monad-EitherDAST = ASTreturn
    Monad._>>=_  Monad-EitherDAST = ASTbind

    EitherDASTExt-MonadMaybeD : MonadMaybeD EitherDExt
    MonadMaybeD.monad  EitherDASTExt-MonadMaybeD = Monad-EitherDAST
    MonadMaybeD.maybeD EitherDASTExt-MonadMaybeD = EitherD-maybe

  bail : ∀ {A} → Err → EitherDExt A
  bail a = ASTop (Left (Either-bail a)) λ ()

  return : ∀ {A} → A → EitherDExt A
  return a = ASTreturn a

