{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Core where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

record ASTOps : Set₂ where
  field
    Cmd  : (A : Set) → Set₁
    Arr : {A : Set} (c : Cmd A) → Set₁
    Sub  : {A : Set} (c : Cmd A) →  Set
open ASTOps

data AST (OP : ASTOps) : Set → Set₁ where
  ASTreturn : ∀ {A} → A → AST OP A
  ASTbind   : ∀ {A B} → (m : AST OP A) (f : A → AST OP B)
              → AST OP B
  ASTop : ∀ {A} → (c : Cmd OP A) (f : Arr OP c → AST OP (Sub OP c)) → AST OP A

record ASTTypes : Set₁ where
  constructor mkASTTypes
  field
    Input  : Set
    Output : (A : Set) → Set

  M : Set → Set
  M A = (i : Input) → Output A

  Pre : Set₁
  Pre = (i : Input) → Set

  Post : Set → Set₁
  Post A = (o : Output A) → Set

  PredTrans : (A : Set) → Set₁
  PredTrans A = (P : Post A) → Pre

  _⊆ᵢ_ : (P₁ P₂ : Pre) → Set
  P₁ ⊆ᵢ P₂ = ∀ i → P₁ i → P₂ i

  _⊆ₒ_ : ∀ {A} → (P₁ P₂ : Post A) → Set
  P₁ ⊆ₒ P₂ = ∀ o → P₁ o → P₂ o

  _⊑_ : {A : Set} → (pt₁ pt₂ : PredTrans A) → Set₁
  pt₁ ⊑ pt₂ = ∀ P → pt₁ P ⊆ᵢ pt₂ P

  MonoPredTrans : ∀ {A} → PredTrans A → Set₁
  MonoPredTrans pt = ∀ P₁ P₂ → (P₁⊆ₒP₂ : P₁ ⊆ₒ P₂) → pt P₁ ⊆ᵢ pt P₂

record ASTOpSem (OP : ASTOps) (Ty : ASTTypes) : Set₁ where
  constructor mkASTOpSem
  open ASTTypes Ty
  field
    runAST : ∀ {A} → (m : AST OP A) → M A

record ASTPredTrans (OP : ASTOps) (Ty : ASTTypes) : Set₂ where
  constructor mkASTPredTrans
  open ASTTypes Ty
  field
    returnPT : ∀ {A} → A → PredTrans A
    bindPT   : ∀ {A B} → (f : A → PredTrans B) (i : Input)
                → (P : Post B) → Post A
    opPT     : ∀ {A} → (c : Cmd OP A) → (Arr OP c → PredTrans (Sub OP c)) → PredTrans A

  predTrans : ∀ {A} → AST OP A → PredTrans A
  predTrans (ASTreturn x) P i =
    returnPT x P i
  predTrans (ASTbind x f) P i =
    predTrans x (bindPT (predTrans ∘ f) i P) i
  predTrans (ASTop c f) P i =
    opPT c (predTrans ∘ f) P i

record ASTPredTransMono {OP : ASTOps} {Ty : ASTTypes} (PT : ASTPredTrans OP Ty) : Set₂ where
  open ASTTypes Ty
  open ASTPredTrans PT
  field
    returnPTMono : ∀ {A} → (x : A) → MonoPredTrans (returnPT x)
    bindPTMono₁  : ∀ {A B} → (f : A → PredTrans B)
                   → (∀ x → MonoPredTrans (f x))
                   → ∀ i P₁ P₂ → P₁ ⊆ₒ P₂ → bindPT f i P₁ ⊆ₒ bindPT f i P₂
    bindPTMono₂  : ∀ {A B} → (f₁ f₂ : A → PredTrans B)
                   → (f₁⊑f₂ : ∀ x → f₁ x ⊑ f₂ x)
                   → ∀ i P → bindPT f₁ i  P ⊆ₒ bindPT f₂ i P
    opPTMono₁    : ∀ {A} (c : Cmd OP A) (f : Arr OP c → PredTrans (Sub OP c))
                   → (∀ r → MonoPredTrans (f r))
                   → ∀ P₁ P₂ → P₁ ⊆ₒ P₂ → opPT c f P₁ ⊆ᵢ opPT c f P₂
    opPTMono₂    : ∀ {A} (c : Cmd OP A) (f₁ f₂ : Arr OP c → PredTrans (Sub OP c))
                   → (f₁⊑f₂ : ∀ r → f₁ r ⊑ f₂ r)
                   → opPT c f₁ ⊑ opPT c f₂

  predTransMono : ∀ {A} (m : AST OP A)
                  → MonoPredTrans (predTrans m)
  predTransMono (ASTreturn x) =
    returnPTMono x
  predTransMono (ASTbind m f) P₁ P₂ P₁⊆P₂ i x₁ =
    predTransMono  m _ _
      (bindPTMono₁ (predTrans ∘ f) (predTransMono ∘ f) i _ _ P₁⊆P₂) i x₁
  predTransMono (ASTop c f) P₁ P₂ P₁⊆P₂ i wp =
    opPTMono₁ c (predTrans ∘ f) (predTransMono ∘ f) _ _ P₁⊆P₂ i wp

record ASTSufficientPT
  {OP : ASTOps} {Ty : ASTTypes}
  (OpSem : ASTOpSem OP Ty) (PT : ASTPredTrans OP Ty) : Set₁ where
  constructor mkASTSufficientPT
  open ASTTypes     Ty
  open ASTOpSem     OpSem
  open ASTPredTrans PT

  Sufficient : (A : Set) (m : AST OP A) → Set₁
  Sufficient A m =
    ∀ P i → (wp : predTrans m P i) → P (runAST m i)

  field
    returnSuf : ∀ {A} x → Sufficient A (ASTreturn x)
    bindSuf   : ∀ {A B} (m : AST OP A) (f : A → AST OP B)
                → (mSuf : Sufficient A m)
                → (fSuf : ∀ x → Sufficient B (f x))
                → Sufficient B (ASTbind m f)
    opSuf     : ∀ {A} → (c : Cmd OP A) (f : Arr OP c → AST OP (Sub OP c))
                → (fSuf : ∀ r → Sufficient (Sub OP c) (f r))
                → Sufficient A (ASTop c f)

  sufficient : ∀ {A} → (m : AST OP A) → Sufficient A m
  sufficient (ASTreturn x) =
    returnSuf x
  sufficient (ASTbind m f) =
    bindSuf m f (sufficient m) (sufficient ∘ f)
  sufficient (ASTop c f) =
    opSuf c f (sufficient ∘ f)

