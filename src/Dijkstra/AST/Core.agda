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
open import Relation.Binary.PropositionalEquality

record ASTOps : Set₂ where
  field
    Cmd     : (A : Set) → Set₁
    SubArg  : {A : Set} (c : Cmd A) → Set₁
    SubRet  : {A : Set} {c : Cmd A} (r : SubArg c) →  Set
open ASTOps

data AST (OP : ASTOps) : Set → Set₁ where
  ASTreturn : ∀ {A} → A                                   → AST OP A
  ASTbind   : ∀ {A B} → (m : AST OP A) (f : A → AST OP B) → AST OP B
  ASTop : ∀ {A} → (c : Cmd OP A)
                  (f : (r : SubArg OP c) → AST OP (SubRet OP r))
                                                          → AST OP A

record ASTTypes : Set₁ where
  constructor mkASTTypes
  field
    Input  : Set
    Output : (A : Set) → Set

  Exec : Set → Set
  Exec A = (i : Input) → Output A

  Pre : Set₁
  Pre = (i : Input) → Set

  Post : Set → Set₁
  Post A = (o : Output A) → Set

  PredTrans : (A : Set) → Set₁
  PredTrans A = (P : Post A) → Pre

  _⊆ᵢ_ : (Pre₁ Pre₂ : Pre) → Set
  Pre₁ ⊆ᵢ Pre₂ = ∀ i → Pre₁ i → Pre₂ i

  _⊆ₒ_ : ∀ {A} → (Post₁ Post₂ : Post A) → Set
  Post₁ ⊆ₒ Post₂ = ∀ o → Post₁ o → Post₂ o

  _⊑_ : {A : Set} → (pt₁ pt₂ : PredTrans A) → Set₁
  pt₁ ⊑ pt₂ = ∀ Post → pt₁ Post ⊆ᵢ pt₂ Post

  MonoPredTrans : ∀ {A} → PredTrans A → Set₁
  MonoPredTrans pt = ∀ Post₁ Post₂ → Post₁ ⊆ₒ Post₂ → pt Post₁ ⊆ᵢ pt Post₂

  -- an abbreviation
  MonoPT = MonoPredTrans

record ASTOpSem (OP : ASTOps) (Ty : ASTTypes) : Set₁ where
  constructor mkASTOpSem
  open ASTTypes Ty
  field
    runAST : ∀ {A} → (m : AST OP A) → Exec A

record ASTPredTrans (OP : ASTOps) (Ty : ASTTypes) : Set₂ where
  constructor mkASTPredTrans
  open ASTTypes Ty
  field
    returnPT : ∀ {A} → A
               → PredTrans A
    bindPT   : ∀ {A B} → (f : A → PredTrans B) (i : Input)
               → (P : Post B) → Post A
    opPT     : ∀ {A} → (c : Cmd OP A)
               → ((r : SubArg OP c) → PredTrans (SubRet OP r))
               → PredTrans A

  predTrans : ∀ {A} → AST OP A → PredTrans A
  predTrans (ASTreturn x) P i =
    returnPT x P i
  predTrans (ASTbind x f) P i =
    predTrans x (bindPT (predTrans ∘ f) i P) i
  predTrans (ASTop c f) P i =
    opPT c (predTrans ∘ f) P i

record ASTPredTransMono {OP} {Ty} (PT : ASTPredTrans OP Ty) : Set₂ where
  open ASTTypes Ty
  open ASTPredTrans PT
  field
    returnPTMono : ∀ {A} → (x : A) → MonoPT (returnPT x)
    bindPTMono   : ∀ {A B} → (f₁ f₂ : A → PredTrans B)
                   → (∀ x → MonoPT (f₁ x)) → (∀ x → MonoPT (f₂ x))
                   → (∀ x → f₁ x ⊑ f₂ x)
                   → ∀ i P₁ P₂ → P₁ ⊆ₒ P₂ → bindPT f₁ i P₁ ⊆ₒ bindPT f₂ i P₂
    opPTMono     : ∀ {A} (c : Cmd OP A)
                     (f₁ f₂ : (r : SubArg OP c) → PredTrans (SubRet OP r))
                   → (∀ r → MonoPT (f₁ r)) → (∀ r → MonoPT (f₂ r))
                   → (∀ r → f₁ r ⊑ f₂ r)
                   → ∀ P₁ P₂ i → P₁ ⊆ₒ P₂ → opPT c f₁ P₁ i → opPT c f₂ P₂ i

  predTransMono : ∀ {A} (m : AST OP A) → MonoPT (predTrans m)
  predTransMono (ASTreturn x) P₁ P₂ P₁⊆P₂ i p = returnPTMono x _ _ P₁⊆P₂ i p
  predTransMono (ASTbind m f) P₁ P₂ P₁⊆P₂ i p =
    predTransMono m _ _
      (bindPTMono p' p' mono mono (λ _ _ _ x → x) i _ _ P₁⊆P₂) i p
    where
    p' = predTrans ∘ f
    mono = predTransMono ∘ f
  predTransMono (ASTop c f) P₁ P₂ P₁⊆P₂ i p =
    opPTMono c (predTrans ∘ f) (predTrans ∘ f) (predTransMono ∘ f) (predTransMono ∘ f)
      (λ _ _ _ x → x) _ _ i P₁⊆P₂ p

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
    returnSuf : ∀ {A} x  → Sufficient A (ASTreturn x)
    bindSuf   : ∀ {A B} (m : AST OP A) (f : A → AST OP B)
                → Sufficient A m
                → (∀ x → Sufficient B (f x))
                → Sufficient B (ASTbind m f)
    opSuf     : ∀ {A} → (c : Cmd OP A) (f : (r : SubArg OP c) → AST OP (SubRet OP r))
                → (∀ r → Sufficient (SubRet OP r) (f r))
                → Sufficient A (ASTop c f)

  sufficient : ∀ {A} → (m : AST OP A) → Sufficient A m
  sufficient (ASTreturn x) =
    returnSuf x
  sufficient (ASTbind m f) =
    bindSuf m f (sufficient m) (sufficient ∘ f)
  sufficient (ASTop c f) =
    opSuf c f (sufficient ∘ f)

record ASTNecessaryPT
  {OP : ASTOps} {Ty : ASTTypes}
  (OpSem : ASTOpSem OP Ty) (PT : ASTPredTrans OP Ty) : Set₁ where
  constructor mkASTNecessaryPT
  open ASTTypes     Ty
  open ASTOpSem     OpSem
  open ASTPredTrans PT

  Necessary : (A : Set) → AST OP A → Set₁
  Necessary A m =
    ∀ P i → P (runAST m i) → predTrans m P i

  field
    returnNec : ∀ {A} x → Necessary A (ASTreturn x)
    bindNec   : ∀ {A B} (m : AST OP A) (f : A → AST OP B)
                → (mNec : Necessary A m)
                → (fNec : ∀ x → Necessary B (f x))
                → Necessary B (ASTbind m f)
    opNec     : ∀ {A} → (c : Cmd OP A) (f : (r : SubArg OP c) → AST OP (SubRet OP r))
                → (fNec : ∀ r → Necessary (SubRet OP r) (f r))
                → Necessary A (ASTop c f)

  necessary : ∀ {A} → (m : AST OP A) → Necessary A m
  necessary {A} (ASTreturn x) =
    returnNec x
  necessary     (ASTbind m f) =
    bindNec m f (necessary m) (necessary ∘ f)
  necessary     (ASTop c f)   =
    opNec c f (necessary ∘ f)

