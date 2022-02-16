{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_)
open import Data.Unit
open import Haskell.Prelude
import      Level
open import Relation.Binary.PropositionalEquality

data AST (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set → Set₁ where
  -- monadic operations
  ASTreturn : ∀ {A} → A → AST C R A
  ASTbind   : ∀ {A B} → AST C R A → (A → AST C R B) → AST C R B
  -- effect operations
  ASTop : ∀ {A} → (c : C A) → (R A c → AST C R A) → AST C R A

record ASTOpSem (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₁ where
  constructor mkASTOpSem
  field
    M       : Set → Set
    returnI : ∀ {A} → A → M A
    bindI   : ∀ {A B} → M A → (A → M B) → M B
    opI     : ∀ {A} → (c : C A) → (R A c → M A) → M A

runAST : ∀ {C R A} → (i : ASTOpSem C R) → AST C R A → ASTOpSem.M i A
runAST i (ASTreturn x) = ASTOpSem.returnI i x
runAST i (ASTbind p f) = ASTOpSem.bindI i (runAST i p) (λ x → runAST i (f x))
runAST i (ASTop c f) = ASTOpSem.opI i c (λ x → runAST i (f x))

record ASTPredTrans (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₂ where
  constructor mkASTPredTrans
  field
    Pre  : Set₁
    Post : (A : Set) → Set₁

  PredTrans : (A : Set) → Set₁
  PredTrans A = Post A → Pre
  
  field
    returnPTS : ∀ {A} → A → PredTrans A
    bindPTS   : ∀ {A B} → (A → PredTrans B) → Post B → Post A
    opPTS     : ∀ {A} → (c : C A) → (R A c → PredTrans A) → PredTrans A

wpAST : ∀ {C R A} → (pt : ASTPredTrans C R) → AST C R A → ASTPredTrans.PredTrans pt A
wpAST pt (ASTreturn x) = ASTPredTrans.returnPTS pt x
wpAST pt (ASTbind p f) Post = wpAST pt p (ASTPredTrans.bindPTS pt (λ x → wpAST pt (f x)) Post)
wpAST pt (ASTop c f) Post = ASTPredTrans.opPTS pt c (λ r → wpAST pt (f r)) Post


module RWS (Ev Wr St : Set) where

  data C (A : Set) : Set₁ where
    RWSgets  : (St → A) → C A
    RWSputs  : (St → St) → A ≡ Unit → C A
    RWSask   : (A ≡ Ev) → C A
    RWSlocal : (Ev → Ev) → C A
    RWStell  : List Wr → (A ≡ Unit) → C A

  R : (A : Set) (c : C A) → Set₁
  R A (RWSgets x) = Level.Lift _ ⊥
  R .Unit (RWSputs f refl) = Level.Lift _ ⊥
  R .Ev (RWSask refl) = Level.Lift _ ⊥
  R A (RWSlocal x) = Level.Lift _ ⊤
  R A (RWStell x refl) = Level.Lift _ ⊥

  RWSOpSem : ASTOpSem C R
  ASTOpSem.M       RWSOpSem A = (ev : Ev) (st : St) → A × St × List Wr
  ASTOpSem.returnI RWSOpSem x ev st = x , st , []
  ASTOpSem.bindI   RWSOpSem x f ev st =
    let (x₁ , st₁ , outs₁) = x ev st
        (x₂ , st₂ , outs₂) = f x₁ ev st₁
    in x₂ , st₂ , outs₁ ++ outs₂
  ASTOpSem.opI     RWSOpSem (RWSgets g) f ev st =
    (g st) , st , []
  ASTOpSem.opI     RWSOpSem (RWSputs p refl) f ev st =
    unit , p st , []
  ASTOpSem.opI     RWSOpSem (RWSask refl) f ev st =
    ev , st , []
  ASTOpSem.opI     RWSOpSem (RWSlocal l) f ev st =
    f (Level.lift _) (l ev) st
  ASTOpSem.opI     RWSOpSem (RWStell t refl) f ev st =
    unit , st , t

module Branching where
  data C (A : Set) : Set₁ where
    ASTif : Guards Unit → C A
    ASTeither : (A₁ A₂ : Set) → Either A₁ A₂ → C A
    ASTmaybe  : (A₁ : Set) → Maybe A₁ → C A

  R : (A : Set) (c : C A) → Set₁
  R A (ASTif gs) = Level.Lift _ (Fin (lengthGuards gs))
  R A (ASTeither A₁ A₂ _) = Level.Lift _ (Either A₁ A₂)
  R A (ASTmaybe A₁ _)     = Level.Lift _ (Maybe A₁)

-- module _ {X : Set → Set}
--   (r : ∀ {A} → A → X A) (b : ∀ {A B} → X A → (A → X B) → X B)
--   where

--   runAST : ∀ {C R A} → AST C R A → (∀ {A} → (c : C A) → (R A c → X A) → X A) → X A
--   runAST (ASTreturn x) op = r x
--   runAST (ASTbind x f) op = b (runAST x op) (λ y → runAST (f y) op)
--   runAST (ASTop c f)   op = op c (λ ret → runAST (f ret) op)

private
  module BranchExtend
    (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
    (interp : ASTOpSem C R)
    where

    CBranch : Set → Set₁
    CBranch A = Either (C A) (Branching.C A)

    RBranch : (A : Set) (c : CBranch A) → Set₁
    RBranch A (Left x) = R A x
    RBranch A (Right y) = Branching.R A y

    interpGuards : ∀ {A : Set} (gs : Guards{b = Level.zero} Unit) (f : Level.Lift (Level.suc Level.zero) (Fin (lengthGuards gs)) → ASTOpSem.M interp A)
                   → ASTOpSem.M interp A
    interpGuards (otherwise≔ x) f = f (Level.lift zero)
    interpGuards (clause (x ≔ x₁) gs) f
      with toBool x
    ... | false = interpGuards gs λ { (Level.lift n) → f (Level.lift (suc n))}
    ... | true = f (Level.lift zero)

    Interp : ASTOpSem CBranch RBranch
    ASTOpSem.M       Interp = ASTOpSem.M interp
    ASTOpSem.returnI Interp = ASTOpSem.returnI interp
    ASTOpSem.bindI   Interp = ASTOpSem.bindI interp
    ASTOpSem.opI     Interp (Left c) f = ASTOpSem.opI interp c f
    ASTOpSem.opI     Interp (Right (Branching.ASTif gs)) f = interpGuards gs f
    ASTOpSem.opI     Interp (Right (Branching.ASTeither A₁ A₂ x₁)) f = f (Level.lift x₁)
    ASTOpSem.opI     Interp (Right (Branching.ASTmaybe A₁ x₁)) f = f (Level.lift x₁)
