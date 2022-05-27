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
  BCif     :               Bool       → BranchCmd A
  BCeither : {B C : Set} → Either B C → BranchCmd A
  BCmaybe  : {B   : Set} → Maybe  B   → BranchCmd A

BranchSubArg : {A : Set} → BranchCmd A → Set₁
BranchSubArg (BCif           x) = Level.Lift _ Bool
BranchSubArg (BCeither{B}{C} x) = Level.Lift _ (Either B C)
BranchSubArg (BCmaybe {B}    x) = Level.Lift _ (Maybe  B)

BranchSubRet : {A : Set} {c : BranchCmd A} → BranchSubArg c → Set
BranchSubRet{A} {BCif     x} _ = A
BranchSubRet{A} {BCeither x} _ = A
BranchSubRet{A} {BCmaybe  x} _ = A

module ASTExtension (O : ASTOps) where

  BranchOps : ASTOps
  ASTOps.Cmd  BranchOps A = Either (ASTOps.Cmd O A) (BranchCmd A)
  ASTOps.SubArg BranchOps{_} (Left x)   = ASTOps.SubArg O x
  ASTOps.SubArg BranchOps{_} (Right y)  = BranchSubArg y
  ASTOps.SubRet BranchOps{_} {(Left x)} r  = ASTOps.SubRet O r
  ASTOps.SubRet BranchOps{_} {(Right y)} r = BranchSubRet r

  unextend : ∀ {A} → AST BranchOps A → AST O A
  unextend (ASTreturn x)      = ASTreturn x
  unextend (ASTbind m f)      = ASTbind (unextend m) (unextend ∘ f)
  unextend (ASTop (Left c) f) = ASTop c (unextend ∘ f)
  unextend (ASTop (Right (BCif false))         f) = unextend (f (Level.lift false))
  unextend (ASTop (Right (BCif true))          f) = unextend (f (Level.lift true))
  unextend (ASTop (Right (BCeither (Left x)))  f) = unextend (f (Level.lift (Left x)))
  unextend (ASTop (Right (BCeither (Right y))) f) = unextend (f (Level.lift (Right y)))
  unextend (ASTop (Right (BCmaybe nothing))    f) = unextend (f (Level.lift nothing))
  unextend (ASTop (Right (BCmaybe (just x)))   f) = unextend (f (Level.lift (just x)))

module BranchingSyntax (O : ASTOps) where
  open ASTExtension O

  ifAST_then_else : ∀ {A} → Bool → (t e : AST BranchOps A) → AST BranchOps A
  ifAST b then t else e = ASTop (Right (BCif b))
                                λ { (Level.lift true)  → t
                                  ; (Level.lift false) → e
                                  }

  eitherAST : ∀ {A B C : Set}
              → (A → AST BranchOps C)
              → (B → AST BranchOps C)
              → Either A B
              → AST BranchOps C
  eitherAST fA fB eAB = ASTop (Right (BCeither eAB))
                              λ { (Level.lift (Left  a)) → fA a
                                ; (Level.lift (Right b)) → fB b
                                }

  -- Same but with arguments in more "natural" order
  eitherSAST : ∀ {A B C : Set}
               → Either A B
               → (A → AST BranchOps C)
               → (B → AST BranchOps C)
               → AST BranchOps C
  eitherSAST eAB fA fB = eitherAST fA fB eAB

module OpSemExtension {O : ASTOps} {T : ASTTypes} (OpSem : ASTOpSem O T) where
  open ASTExtension O

  BranchOpSem : ASTOpSem BranchOps T
  ASTOpSem.runAST BranchOpSem m i = ASTOpSem.runAST OpSem (unextend m) i

module PredTransExtension {O : ASTOps} {T : ASTTypes} (PT : ASTPredTrans O T) where
  open ASTExtension O

  BranchPT : ASTPredTrans BranchOps T
  ASTPredTrans.returnPT BranchPT = ASTPredTrans.returnPT PT
  ASTPredTrans.bindPT   BranchPT = ASTPredTrans.bindPT   PT
  ASTPredTrans.opPT     BranchPT (Left x) =
    ASTPredTrans.opPT PT x
  ASTPredTrans.opPT     BranchPT (Right (BCif c))     f P i =
      (       c ≡ true    → f (Level.lift true) P i)
    × (       c ≡ false   → f (Level.lift false) P i)
  ASTPredTrans.opPT     BranchPT (Right (BCeither e)) f P i =
      (∀ l →  e ≡ Left  l → f (Level.lift (Left l))  P i)
    × (∀ r →  e ≡ Right r → f (Level.lift (Right r)) P i)
  ASTPredTrans.opPT     BranchPT (Right (BCmaybe mb)) f P i =
      (      mb ≡ nothing → f (Level.lift nothing)   P i)
    × (∀ j → mb ≡ just j  → f (Level.lift (just j))  P i)
  open ASTPredTrans BranchPT

module PredTransExtensionMono
  {O : ASTOps} {T : ASTTypes} {PT : ASTPredTrans O T}
  (M : ASTPredTransMono PT) where
  open ASTTypes T hiding (M)
  open ASTExtension O
  open PredTransExtension PT

  BranchPTMono : ASTPredTransMono BranchPT
  ASTPredTransMono.returnPTMono BranchPTMono = ASTPredTransMono.returnPTMono M
  ASTPredTransMono.bindPTMono₁ BranchPTMono = ASTPredTransMono.bindPTMono₁ M
  ASTPredTransMono.bindPTMono₂ BranchPTMono = ASTPredTransMono.bindPTMono₂ M
  ASTPredTransMono.opPTMono₁ BranchPTMono (Left x) = ASTPredTransMono.opPTMono₁ M x
  proj₁ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCif x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) refl =
    monoF (Level.lift true) _ _ P₁⊆ₒP₂ i (proj₁ wp refl)
  proj₂ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCif x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) refl =
    monoF (Level.lift false) _ _ P₁⊆ₒP₂ i (proj₂ wp refl)
  proj₁ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCeither x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) l refl =
    monoF (Level.lift (Left l)) _ _ P₁⊆ₒP₂ i (proj₁ wp _ refl)
  proj₂ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCeither x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) r refl =
    monoF (Level.lift (Right r)) _ _ P₁⊆ₒP₂ i (proj₂ wp _ refl)
  proj₁ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCmaybe x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) refl =
    monoF (Level.lift nothing) _ _ P₁⊆ₒP₂ i (proj₁ wp refl)
  proj₂ (ASTPredTransMono.opPTMono₁ BranchPTMono (Right (BCmaybe x)) f monoF P₁ P₂ P₁⊆ₒP₂ i wp) j refl =
    monoF (Level.lift (just j)) _ _ P₁⊆ₒP₂ i (proj₂ wp _ refl)
  ASTPredTransMono.opPTMono₂ BranchPTMono (Left x) = ASTPredTransMono.opPTMono₂ M x
  proj₁ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCif x)) f₁ f₂ f₁⊑f₂ P i wp) refl =
    f₁⊑f₂ (Level.lift true) _ i (proj₁ wp refl)
  proj₂ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCif x)) f₁ f₂ f₁⊑f₂ P i wp) refl =
    f₁⊑f₂ (Level.lift false) _ i (proj₂ wp refl)
  proj₁ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCeither x)) f₁ f₂ f₁⊑f₂ P i wp) l refl =
    f₁⊑f₂ (Level.lift (Left l)) _ i (proj₁ wp _ refl)
  proj₂ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCeither x)) f₁ f₂ f₁⊑f₂ P i wp) r refl =
    f₁⊑f₂ (Level.lift (Right r)) _ i (proj₂ wp _ refl)
  proj₁ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCmaybe x)) f₁ f₂ f₁⊑f₂ P i wp) refl =
    f₁⊑f₂ (Level.lift nothing) _ i (proj₁ wp refl)
  proj₂ (ASTPredTransMono.opPTMono₂ BranchPTMono (Right (BCmaybe x)) f₁ f₂ f₁⊑f₂ P i wp) j refl =
    f₁⊑f₂ (Level.lift (just j)) _ i (proj₂ wp _ refl)

  unextendPT : ∀ {A} (m : AST BranchOps A)
               → ASTPredTrans.predTrans BranchPT m ⊑ ASTPredTrans.predTrans PT (unextend m)
  unextendPT (ASTreturn x) P i wp = wp
  unextendPT (ASTbind m f) P i wp =
    ASTPredTransMono.predTransMono M (unextend m) _ _ 
      (ASTPredTransMono.bindPTMono₂ M _ _ (unextendPT ∘ f) i P)
      i (unextendPT m _ _ wp)
  unextendPT (ASTop (Left x) f) P i wp =
    ASTPredTransMono.opPTMono₂ M x _ _ (unextendPT ∘ f) P i wp
  unextendPT (ASTop (Right (BCif false)) f) P i wp =
    unextendPT (f (Level.lift false)) P i (proj₂ wp refl)
  unextendPT (ASTop (Right (BCif true)) f) P i wp =
    unextendPT (f (Level.lift true)) _ _ (proj₁ wp refl)
  unextendPT (ASTop (Right (BCeither (Left x))) f) P i wp =
    unextendPT (f (Level.lift (Left x))) _ _ (proj₁ wp _ refl)
  unextendPT (ASTop (Right (BCeither (Right y))) f) P i wp =
    unextendPT (f (Level.lift (Right y))) _ _ (proj₂ wp _ refl)
  unextendPT (ASTop (Right (BCmaybe nothing)) f) P i wp =
    unextendPT (f (Level.lift nothing)) _ _ (proj₁ wp refl)
  unextendPT (ASTop (Right (BCmaybe (just j))) f) P i wp =
    unextendPT (f (Level.lift (just j))) _ _ (proj₂ wp _ refl)

  extendPT : ∀ {A} (m : AST BranchOps A)
             → ASTPredTrans.predTrans PT (unextend m) ⊑ ASTPredTrans.predTrans BranchPT m
  extendPT (ASTreturn x) P i wp = wp
  extendPT (ASTbind m f) P i wp =
    ASTPredTransMono.predTransMono BranchPTMono m _ _
      (ASTPredTransMono.bindPTMono₂ BranchPTMono _ _ (extendPT ∘ f) _ _) _
      (extendPT m _ _ wp)
  extendPT (ASTop (Left x) f) P i wp =
    ASTPredTransMono.opPTMono₂ BranchPTMono (Left x) _ _ (extendPT ∘ f) _ _ wp
  proj₁ (extendPT (ASTop (Right (BCif x)) f) P i wp) refl =
    extendPT (f (Level.lift true)) _ _ wp
  proj₂ (extendPT (ASTop (Right (BCif x)) f) P i wp) refl =
    extendPT (f (Level.lift false)) _ _ wp
  proj₁ (extendPT (ASTop (Right (BCeither x)) f) P i wp) l refl =
    extendPT (f (Level.lift (Left l))) _ _ wp
  proj₂ (extendPT (ASTop (Right (BCeither x)) f) P i wp) r refl =
    extendPT (f (Level.lift (Right r))) _ _ wp
  proj₁ (extendPT (ASTop (Right (BCmaybe x)) f) P i wp) refl =
    extendPT (f (Level.lift nothing)) _ _ wp
  proj₂ (extendPT (ASTop (Right (BCmaybe x)) f) P i wp) j refl =
    extendPT (f (Level.lift (just j))) _ _ wp

module SufficientExtension
  {O : ASTOps} {T : ASTTypes} {OS : ASTOpSem O T} {PT : ASTPredTrans O T}
  (M : ASTPredTransMono PT) (S : ASTSufficientPT OS PT) where
  open ASTTypes T hiding (M)
  open ASTExtension O
  open OpSemExtension OS
  open PredTransExtension PT
  open PredTransExtensionMono M

  BranchSuf : ASTSufficientPT BranchOpSem BranchPT
  ASTSufficientPT.returnSuf BranchSuf = ASTSufficientPT.returnSuf S
  ASTSufficientPT.bindSuf BranchSuf m f mSuf fSuf P i wp =
    ASTSufficientPT.bindSuf S (unextend m) (unextend ∘ f) mSuf' fSuf' _ _ wp'
    where
    mSuf' : ASTSufficientPT.Sufficient S _ (unextend m)
    mSuf' P i wp = mSuf _ _ (extendPT m _ _ wp)

    fSuf' : ∀ x → ASTSufficientPT.Sufficient S _ (unextend (f x))
    fSuf' x P i wp = fSuf x _ _ (extendPT (f x) _ _ wp)

    wp' : ASTPredTrans.predTrans PT (ASTbind (unextend m) (unextend ∘ f)) P i
    wp' = unextendPT (ASTbind m f) _ _ wp
  ASTSufficientPT.opSuf BranchSuf (Left x) f fSuf P i wp =
    ASTSufficientPT.opSuf S x (unextend ∘ f) fSuf' _ _ wp'
    where
    fSuf' : ∀ r → ASTSufficientPT.Sufficient S _ (unextend (f r))
    fSuf' r P i wp = fSuf r _ _ (extendPT (f r) _ _ wp)

    wp' : ASTPredTrans.predTrans PT (ASTop x (unextend ∘ f)) _ _
    wp' = unextendPT (ASTop (Left x) f) _ _ wp
  ASTSufficientPT.opSuf BranchSuf (Right (BCif false)) f fSuf P i wp =
    fSuf (Level.lift false) _ _ (proj₂ wp refl)
  ASTSufficientPT.opSuf BranchSuf (Right (BCif true)) f fSuf P i wp =
    fSuf (Level.lift true) _ _ (proj₁ wp refl)
  ASTSufficientPT.opSuf BranchSuf (Right (BCeither (Left x))) f fSuf P i wp =
    fSuf (Level.lift (Left x)) _ _ (proj₁ wp _ refl)
  ASTSufficientPT.opSuf BranchSuf (Right (BCeither (Right y))) f fSuf P i wp =
    fSuf (Level.lift (Right y)) _ _ (proj₂ wp _ refl)
  ASTSufficientPT.opSuf BranchSuf (Right (BCmaybe nothing)) f fSuf P i wp =
    fSuf (Level.lift nothing) _ _ (proj₁ wp refl)
  ASTSufficientPT.opSuf BranchSuf (Right (BCmaybe (just j))) f fSuf P i wp =
    fSuf (Level.lift (just j)) _ _ (proj₂ wp _ refl)
