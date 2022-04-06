{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Branching where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Dijkstra.AST.Core
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

data BranchCmd (A : Set) : Set₁ where
  BCif     : Bool → BranchCmd A
  BCeither : {B C : Set} → Either B C → BranchCmd A

BranchResp : {A : Set} → BranchCmd A → Set₁
BranchResp (BCif x) = Level.Lift _ Bool
BranchResp (BCeither{B}{C} x) = Level.Lift _ (Either B C)

BranchSub : {A : Set} → BranchCmd A → Set
BranchSub{A} (BCif x) = A
BranchSub{A} (BCeither x) = A

module ASTExtension (O : ASTOps) where

  BranchOps : ASTOps
  ASTOps.Cmd  BranchOps A = Either (ASTOps.Cmd O A) (BranchCmd A)
  ASTOps.Resp BranchOps (Left x)  = ASTOps.Resp O x
  ASTOps.Resp BranchOps (Right y) = BranchResp y
  ASTOps.Sub  BranchOps  (Left x)  = ASTOps.Sub O x
  ASTOps.Sub  BranchOps  (Right y) = BranchSub y

  unextend : ∀ {A} → AST BranchOps A → AST O A
  unextend (ASTreturn x) = ASTreturn x
  unextend (ASTbind m f) = ASTbind (unextend m) (unextend ∘ f)
  unextend (ASTop (Left c) f) = ASTop c (unextend ∘ f)
  unextend (ASTop (Right (BCif false)) f) = unextend (f (Level.lift false))
  unextend (ASTop (Right (BCif true)) f) = unextend (f (Level.lift true))
  unextend (ASTop (Right (BCeither (Left x))) f) = unextend (f (Level.lift (Left x)))
  unextend (ASTop (Right (BCeither (Right y))) f) = unextend (f (Level.lift (Right y)))

module OpSemExtension {O : ASTOps} {T : ASTTypes} (OpSem : ASTOpSem O T) where
  open ASTExtension O

  BranchOpSem : ASTOpSem BranchOps T
  ASTOpSem.runAST BranchOpSem m i = ASTOpSem.runAST OpSem (unextend m) i

module PredTransExtension {O : ASTOps} {T : ASTTypes} (PT : ASTPredTrans O T) where
  open ASTExtension O

  BranchPT : ASTPredTrans BranchOps T
  ASTPredTrans.returnPT BranchPT  = ASTPredTrans.returnPT  PT
  ASTPredTrans.bindPT BranchPT    = ASTPredTrans.bindPT    PT
  ASTPredTrans.opPT BranchPT (Left x) = ASTPredTrans.opPT PT x
  ASTPredTrans.opPT BranchPT (Right (BCif c)) f P i =
      c ≡ true → f (Level.lift true) P i
    × c ≡ false → f (Level.lift false) P i
  ASTPredTrans.opPT BranchPT (Right (BCeither e)) f P i =
      ∀ l → e ≡ Left  l → f (Level.lift (Left l))  P i
    × ∀ r → e ≡ Right r → f (Level.lift (Right r)) P i
