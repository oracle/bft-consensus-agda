{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- As we are interested in using Either for error handling (and providing the Either-bail command
-- for this purpose), we call the Left type "Err"
module Dijkstra.AST.Either (Err : Set) where

open import Dijkstra.AST.Prelude

module EitherBase where

  open import Dijkstra.AST.Core

  data EitherCmd (A : Set) : Set₁ where
    Either-bail : Err → EitherCmd A

  EitherSubArg : {A : Set} (a : EitherCmd A) → Set₁
  EitherSubArg (Either-bail _) = Lift _ Void

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

  open ASTPredTrans  EitherPT
  open ASTPTIWeakest EitherOpSem EitherPT

  predTrans-is-weakest-base' : ∀ {A} → (m : EitherBaseAST A) → Post⇒wp-base {A} m unit
  predTrans-is-weakest-base' (ASTreturn _) _ = id
  predTrans-is-weakest-base' (ASTbind m f) _ Pr
     with predTrans-is-weakest-base' m
  ...| rec
    with runEitherBase m unit
  ... | Left  x = rec _ λ where _ refl → Pr
  ... | Right x = rec _ λ where r refl → predTrans-is-weakest-base' (f x) _ Pr
  predTrans-is-weakest-base' (ASTop (Either-bail _) _) _ = id

  predTrans-is-weakest-base : ∀ {A} → {i : Unit} → (m : EitherBaseAST A) → Post⇒wp-base {A} m i
  predTrans-is-weakest-base {A} {unit} m = predTrans-is-weakest-base' m

  ------------------------------------------------------------------------------
  open ASTPredTransMono
  EitherPTMono : ASTPredTransMono EitherPT
  returnPTMono EitherPTMono                 _                            _  _       P₁⊆ₒP₂ _         wp =
    P₁⊆ₒP₂ _ wp
  bindPTMono   EitherPTMono                 f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ (Left  x) wp .(Left  x) refl =
    P₁⊆ₒP₂ (Left x) (wp (Left x) refl)
  bindPTMono   EitherPTMono                 f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ (Right y) wp .(Right y) refl =
    mono₂ y P₁ P₂ P₁⊆ₒP₂ unit (f₁⊑f₂ y P₁ unit (wp (Right y) refl))
  opPTMono     EitherPTMono (Either-bail x) f₁ f₂ mono₁ mono₂ f₁⊑f₂      P₁ P₂ unit P₁⊆ₒP₂           wp =
    P₁⊆ₒP₂ (Left x) wp

  ------------------------------------------------------------------------------
  open ASTSufficientPT
  EitherSuf : ASTSufficientPT EitherOpSem EitherPT

  returnSuf EitherSuf x P i wp = wp
  bindSuf EitherSuf {A} {B} m f mSuf fSuf P unit wp
     with  runEitherBase m  unit  | inspect
          (runEitherBase m) unit
  ... | Left  x | [ R ] = mSuf _ unit wp (Left x) (sym R)
  ... | Right y | [ R ] = let wp' = mSuf _ unit wp (Right y) (sym R)
                           in fSuf y P unit wp'
  opSuf EitherSuf (Either-bail x) f fSuf P i wp = wp

module EitherAST where
  open EitherBase
  open EitherBase using (EitherbindPost)                                 public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open ConditionalExtensions EitherPT EitherOpSem EitherPTMono EitherSuf public
  open WithPTIWBase predTrans-is-weakest-base                            public

  EitherAST    = ExtAST

  runEitherAST = runAST

module EitherSyntax where
  open import Dijkstra.AST.Core
  open import Dijkstra.AST.Branching
  open import Dijkstra.Syntax
  open ASTExtension
  open EitherBase
  open EitherAST

  EitherAST-maybe : ∀ {A B : Set} → ExtAST B → (A → ExtAST B) → Maybe A → ExtAST B
  EitherAST-maybe m f mb = ASTop (Right (BCmaybe mb))
                                 λ { (lift nothing)  → m
                                   ; (lift (just j)) → f j
                                   }

  bail : ∀ {A} → Err → AST (BranchOps EitherOps) A
  bail a = ASTop (Left (Either-bail a)) λ ()

open        EitherAST       public
open        EitherSyntax    public

module EitherExample where
  open        EitherAST
  open        EitherSyntax

  -- Here we show an EitherAST program in terms of the underlying Cmds, which requires importing
  -- Core and also opening EitherBase
  module _ where
    open import Dijkstra.AST.Core
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
