{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- As we are interested in using Either for error handling (and providing the Either-bail command
-- for this purpose), we call the Left type "Err"
module Dijkstra.AST.Either (Err : Set) where

open import Data.Empty
open import Data.Product using (_×_ ; _,_)
open import Data.Unit
open import Haskell.Prelude hiding (return)
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

module EitherBase where

  open import Dijkstra.AST.Core

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

  EitherBaseAST = AST EitherOps

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

  runEitherBase = ASTOpSem.runAST EitherOpSem

  EitherbindPost : ∀ {A B} → (A → PredTrans B) → Post B → Post A
  EitherbindPost _ P (Left x)  = P (Left x)
  EitherbindPost f P (Right y) = f y P unit

  EitherPT : ASTPredTrans EitherOps EitherTypes
  ASTPredTrans.returnPT EitherPT x P i = P (Right x)
  ASTPredTrans.bindPT EitherPT {A} {B} f i Post x =
    ∀ r → r ≡ x → EitherbindPost f Post r
  ASTPredTrans.opPT EitherPT (Either-bail a) f Post i = Post (Left a)
  open ASTPredTrans EitherPT

  ------------------------------------------------------------------------------
  EitherPTMono : ASTPredTransMono EitherPT

  ASTPredTransMono.returnPTMono EitherPTMono                 x                            _  _       P₁⊆ₒP₂ _         wp =
    P₁⊆ₒP₂ _ wp
  ASTPredTransMono.bindPTMono   EitherPTMono                 f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ (Left  x) wp .(Left  x) refl =
    P₁⊆ₒP₂ (Left x) (wp (Left x) refl)
  ASTPredTransMono.bindPTMono   EitherPTMono                 f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ (Right y) wp .(Right y) refl =
    mono₂ y P₁ P₂ P₁⊆ₒP₂ unit (f₁⊑f₂ y P₁ unit (wp (Right y) refl))
  ASTPredTransMono.opPTMono     EitherPTMono (Either-bail x) f₁ f₂ mono₁ mono₂ f₁⊑f₂      P₁ P₂ unit P₁⊆ₒP₂           wp =
    P₁⊆ₒP₂ (Left x) wp

  ------------------------------------------------------------------------------
  EitherSuf : ASTSufficientPT EitherOpSem EitherPT

  ASTSufficientPT.returnSuf EitherSuf x P i wp = wp
  ASTSufficientPT.bindSuf EitherSuf {A} {B} m f mSuf fSuf P unit wp
     with  runEitherBase m  unit  | inspect
          (runEitherBase m) unit
  ... | Left  x | [ R ] = mSuf _ unit wp (Left x) (sym R)
  ... | Right y | [ R ] = let wp' = mSuf _ unit wp (Right y) (sym R)
                           in fSuf y P unit wp'
  ASTSufficientPT.opSuf EitherSuf (Either-bail x) f fSuf P i wp = wp

module EitherAST where
  open EitherBase
  open EitherBase using (EitherbindPost)                                 public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open ConditionalExtensions EitherPT EitherOpSem EitherPTMono EitherSuf public

  EitherAST    = ExtAST

  runEitherAST = runAST

  -- This property says that predTrans really is the *weakest* precondition for a
  -- postcondition to hold after running a MaybeD.
  Post⇒wp : ∀ {A} → EitherAST A → Input → Set₁
  Post⇒wp {A} e i =
    (P : Post A)
    → P (runEitherAST e i)
    → predTrans e P i

  predTrans-is-weakest : ∀ {A} → (e : EitherAST A) → Post⇒wp {A} e unit
  predTrans-is-weakest (ASTreturn _) _ = id
  predTrans-is-weakest (ASTbind e f) _ Pr
     with predTrans-is-weakest e
  ...| rec
    with runEitherAST e unit
  ... | Left  _ = rec _ λ where _ refl →                              Pr
  ... | Right r = rec _ λ where _ refl → predTrans-is-weakest (f r) _ Pr
  predTrans-is-weakest (ASTop (Left (Either-bail _)) _) _ = id
  -- TODO: this is identical to the same for Maybe -- generalise?
  predTrans-is-weakest (ASTop (Right (BCif b)) f) Pr
     with predTrans-is-weakest (f (Level.lift b))
  ...| rec = λ x → (λ where   refl → rec Pr x) , (λ where   refl → rec Pr x)
  predTrans-is-weakest (ASTop (Right (BCeither b)) f) Pr
     with predTrans-is-weakest (f (Level.lift b))
  ...| rec = λ x → (λ where r refl → rec Pr x) , (λ where r refl → rec Pr x)
  predTrans-is-weakest (ASTop (Right (BCmaybe mb)) f) Pr
     with predTrans-is-weakest (f (Level.lift mb))
  ...| rec = λ x → (λ where   refl → rec Pr x) , (λ where j refl → rec Pr x)

module EitherSyntax where
  open import Dijkstra.AST.Core
  open import Dijkstra.AST.Branching
  open import Dijkstra.Syntax
  open ASTExtension
  open EitherBase
  open EitherAST

  EitherAST-maybe : ∀ {A B : Set} → ExtAST B → (A → ExtAST B) → Maybe A → ExtAST B
  EitherAST-maybe m f mb = ASTop (Right (BCmaybe mb))
                                 λ { (Level.lift nothing)  → m
                                   ; (Level.lift (just j)) → f j
                                   }
  instance
    MonadMaybeD-EitherAST : MonadMaybeD ExtAST
    MonadMaybeD.monad  MonadMaybeD-EitherAST = MonadAST
    MonadMaybeD.maybeD MonadMaybeD-EitherAST = EitherAST-maybe

  bail : ∀ {A} → Err → AST (BranchOps EitherOps) A
  bail a = ASTop (Left (Either-bail a)) λ ()

open        EitherAST       public
open        EitherSyntax    public

module EitherExample where
  open        EitherAST
  open        EitherSyntax
  open import Haskell.Prelude using (return)

  -- Here we show an EitherAST program in terms of the underlying Cmds, which requires importing
  -- Core and also opening EitherBase
  module _ where
    open import Dijkstra.AST.Core
    open import Dijkstra.Syntax
    open        EitherBase

    prog₁ : ∀ {A} → Err → A → EitherAST A
    prog₁ e a =
      -- Either-bail always returns left, so Agda cannot infer the
      -- type that it would return if it were to return Right, so
      -- we provide a type explicitly (Unit, in this case)
      ASTbind (ASTop (Left (Either-bail {Unit} e)) λ ()) λ _ →
        ASTreturn a

  -- Now we present an equivalent program using the EitherSyntax, so we don't need to open
  -- EitherBase, and prove properties about it.  The same proofs work for prog₁ as for prog₁'.
  prog₁' : ∀ {A} → Err → A → EitherAST A
  prog₁' {A} e a = do
    bail {Void} e
    return a

  -- If Either-bail did not work (e.g., if it were a noop), prog₁ would return Right a and the proof
  -- would fail
  BailWorks : ∀ {A : Set} → Err → Post A
  BailWorks e = _≡ Left e

  bailWorks : ∀ e i {A : Set} → (a : A) → predTrans (prog₁' e a) (BailWorks e) i
  bailWorks e unit _ _ refl = refl

  bailWorksSuf : ∀ e {A : Set} (a : A) i → (runEitherAST (prog₁' e a) i ≡ Left e)
  bailWorksSuf e a i = sufficient (prog₁' e a) (BailWorks e) unit (bailWorks e unit a )
