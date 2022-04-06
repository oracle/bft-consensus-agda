{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.RWS (Ev Wr St : Set) where

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

data RWSCmd (A : Set) : Set₁ where
  RWSgets   : (g : St → A)                 → RWSCmd A
  RWSputs   : (p : St → St) → (A ≡ Unit)   → RWSCmd A
  RWSask    : (A ≡ Ev)                     → RWSCmd A
  RWSlocal  : (l : Ev → Ev)                → RWSCmd A
  RWStell   : (out : List Wr) → (A ≡ Unit) → RWSCmd A
  RWSlisten : {A' : Set} → (A ≡ (A' × List Wr)) → RWSCmd A
  RWSpass   :                                RWSCmd A

RWSResp : {A : Set} (c : RWSCmd A) → Set₁
RWSResp (RWSgets g)          = Level.Lift _ ⊥
RWSResp (RWSputs p refl)     = Level.Lift _ ⊥
RWSResp (RWSask refl)        = Level.Lift _ ⊥
RWSResp (RWSlocal l)         = Level.Lift _ ⊤
RWSResp (RWStell out refl)   = Level.Lift _ ⊥
RWSResp (RWSlisten{A'} refl) = Level.Lift _ ⊤
RWSResp  RWSpass             = Level.Lift _ ⊤

RWSSub : {A : Set} (c : RWSCmd A) → Set
RWSSub{A} (RWSgets g) = A
RWSSub{A} (RWSputs p x) = A
RWSSub{A} (RWSask x) = A
RWSSub{A} (RWSlocal l) = A
RWSSub{A} (RWStell out x) = A
RWSSub {.(_ × List Wr)} (RWSlisten{A'} refl) = A'
RWSSub{A} RWSpass = A × (List Wr → List Wr)

RWSOps : ASTOps
ASTOps.Cmd RWSOps  = RWSCmd
ASTOps.Resp RWSOps = RWSResp
ASTOps.Sub  RWSOps = RWSSub

RWS = AST RWSOps

private
  prog₁ : (St → Wr) → RWS ⊤
  prog₁ f =
    ASTop RWSpass λ _ →
      ASTbind (ASTop (RWSgets f) λ ()) λ w →
      ASTbind (ASTop (RWStell (w ∷ []) refl) λ ()) λ _ →
      ASTreturn (tt , λ o → o ++ o)

RWSTypes : ASTTypes
ASTTypes.Input  RWSTypes    = Ev × St
ASTTypes.Output RWSTypes A  = A × St × List Wr

open ASTTypes RWSTypes

RWSOpSem : ASTOpSem RWSOps RWSTypes
ASTOpSem.runAST RWSOpSem (ASTreturn x) (ev , st) = x , st , []
ASTOpSem.runAST RWSOpSem (ASTbind m f) (ev , st₀) =
  let (x₁ , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem m (ev , st₀)
      (x₂ , st₂ , outs₂) = ASTOpSem.runAST RWSOpSem (f x₁) (ev , st₁)
  in (x₂ , st₂ , outs₁ ++ outs₂)
ASTOpSem.runAST RWSOpSem (ASTop (RWSgets g) f) (ev , st) =
  g st , st , []
ASTOpSem.runAST RWSOpSem (ASTop (RWSputs p refl) f) (ev , st) =
  unit , p st , []
ASTOpSem.runAST RWSOpSem (ASTop (RWSask refl) f) (ev , st) =
  ev , st , []
ASTOpSem.runAST RWSOpSem (ASTop (RWSlocal l) f) (ev , st) =
  ASTOpSem.runAST RWSOpSem (f (Level.lift tt)) (l ev , st)
ASTOpSem.runAST RWSOpSem (ASTop (RWStell out refl) f) (ev , st) =
  unit , st , out
ASTOpSem.runAST RWSOpSem (ASTop (RWSlisten refl) f) (ev , st) =
  let (x₁ , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift tt)) (ev , st)
  in (x₁ , outs₁) , st₁ , outs₁
ASTOpSem.runAST RWSOpSem (ASTop RWSpass f) (ev , st) =
  let ((x₁ , wf) , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift tt)) (ev , st)
  in x₁ , st₁ , wf outs₁

runRWS = ASTOpSem.runAST RWSOpSem

RWSbindPost : (outs : List Wr) {A : Set} → Post A → Post A
RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

RWSpassPost : ∀ {A} → Post A → Post (A × (List Wr → List Wr))
RWSpassPost P ((x , f) , s , o) = ∀ o' → o' ≡ f o → P (x , s , o')

RWSlistenPost : ∀ {A} → Post (A × List Wr) → Post A
RWSlistenPost P (x , s , o) = P ((x , o) , s , o)

RWSPT : ASTPredTrans RWSOps RWSTypes
ASTPredTrans.returnPT RWSPT x P (ev , st) =
  P (x , st , [])
ASTPredTrans.bindPT RWSPT f (ev , st) P (x , st' , outs) =
  ∀ r → r ≡ x → f r (RWSbindPost outs P) (ev , st')
ASTPredTrans.opPT RWSPT (RWSgets g) f P (ev , st) =
  P (g st , st , [])
ASTPredTrans.opPT RWSPT (RWSputs p refl) f P (ev , st) =
  P (unit , p st , [])
ASTPredTrans.opPT RWSPT (RWSask refl) f P (ev , st) =
  P (ev , st , [])
ASTPredTrans.opPT RWSPT (RWSlocal l) f P (ev , st) =
  ∀ ev' → ev' ≡ l ev → f (Level.lift tt) P (ev' , st)
ASTPredTrans.opPT RWSPT (RWStell out refl) f P (ev , st) =
  P (unit , st , out)
ASTPredTrans.opPT RWSPT (RWSlisten{A'} refl) f P (ev , st) =
  f (Level.lift tt) (RWSlistenPost P) (ev , st)
ASTPredTrans.opPT RWSPT{A} RWSpass f P (ev , st) =
  f (Level.lift tt) (RWSpassPost P) (ev , st)

private
  TwoOuts : Post ⊤
  TwoOuts (_ , _ , o) = length o ≡ 2

  wpTwoOuts : ∀ f i → ASTPredTrans.predTrans RWSPT (prog₁ f) TwoOuts i
  wpTwoOuts f (e , s) w w= unit refl .(w ∷ w ∷ []) refl = refl

RWSPTMono : ASTPredTransMono RWSPT
ASTPredTransMono.returnPTMono RWSPTMono x P₁ P₂ P₁⊆ₒP₂ i wp =
  P₁⊆ₒP₂ _ wp
ASTPredTransMono.bindPTMono₁ RWSPTMono f monoF (ev , st) P₁ P₂ P₁⊆ₒP₂ (x₁ , st₁ , outs₁) wp .x₁ refl =
  monoF _ _ _ (λ o' pf' → P₁⊆ₒP₂ _ pf') (ev , st₁) (wp _ refl)
ASTPredTransMono.bindPTMono₂ RWSPTMono f₁ f₂ f₁⊑f₂ (ev , st) P (x₁ , st₁ , outs₁) wp .x₁ refl =
  f₁⊑f₂ x₁ (RWSbindPost outs₁ P) (ev , st₁) (wp x₁ refl)
ASTPredTransMono.opPTMono₁ RWSPTMono (RWSgets g) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  P₁⊆ₒP₂ _ wp
ASTPredTransMono.opPTMono₁ RWSPTMono (RWSputs p refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  P₁⊆ₒP₂ _ wp
ASTPredTransMono.opPTMono₁ RWSPTMono (RWSask refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  P₁⊆ₒP₂ _ wp
ASTPredTransMono.opPTMono₁ RWSPTMono (RWSlocal l) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp .(l ev) refl =
  monoF (Level.lift tt) _ _ P₁⊆ₒP₂ (l ev , st) (wp _ refl)
ASTPredTransMono.opPTMono₁ RWSPTMono (RWStell out refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  P₁⊆ₒP₂ _ wp
ASTPredTransMono.opPTMono₁ RWSPTMono (RWSlisten refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  monoF (Level.lift tt) _ _ (λ where (x' , st' , o') → P₁⊆ₒP₂ _) (ev , st) wp
ASTPredTransMono.opPTMono₁ RWSPTMono RWSpass f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
  monoF (Level.lift tt) _ _ (λ where ((x' , w') , st' , o') pf₁ ._ refl → P₁⊆ₒP₂ _ (pf₁ _ refl)) (ev , st) wp
ASTPredTransMono.opPTMono₂ RWSPTMono (RWSgets g) f₁ f₂ f₁⊑f₂ P i wp =
  wp
ASTPredTransMono.opPTMono₂ RWSPTMono (RWSputs p refl) f₁ f₂ f₁⊑f₂ P i wp =
  wp
ASTPredTransMono.opPTMono₂ RWSPTMono (RWSask refl) f₁ f₂ f₁⊑f₂ P i wp =
  wp
ASTPredTransMono.opPTMono₂ RWSPTMono (RWSlocal l) f₁ f₂ f₁⊑f₂ P (ev , st) wp .(l ev) refl =
  f₁⊑f₂ (Level.lift tt) _ _ (wp _ refl)
ASTPredTransMono.opPTMono₂ RWSPTMono (RWStell out refl) f₁ f₂ f₁⊑f₂ P i wp =
  wp
ASTPredTransMono.opPTMono₂ RWSPTMono (RWSlisten refl) f₁ f₂ f₁⊑f₂ P i wp =
  f₁⊑f₂ (Level.lift tt) _ _ wp
ASTPredTransMono.opPTMono₂ RWSPTMono RWSpass f₁ f₂ f₁⊑f₂ P i wp =
  f₁⊑f₂ _ _ _ wp

RWSSuf : ASTSufficientPT RWSOpSem RWSPT
ASTSufficientPT.returnSuf RWSSuf x P i wp = wp
ASTSufficientPT.bindSuf RWSSuf m f mSuf fSuf P (e , s₀) wp =
  let (x₁ , s₁ , o₁) = ASTOpSem.runAST RWSOpSem m (e , s₀)
      wpₘ = mSuf _ (e , s₀) wp _ refl
  in fSuf x₁ _ (e , s₁) wpₘ
ASTSufficientPT.opSuf RWSSuf (RWSgets g) f fSuf P i wp = wp
ASTSufficientPT.opSuf RWSSuf (RWSputs p refl) f fSuf P i wp = wp
ASTSufficientPT.opSuf RWSSuf (RWSask refl) f fSuf P i wp = wp
ASTSufficientPT.opSuf RWSSuf (RWSlocal l) f fSuf P (e , s) wp =
  fSuf (Level.lift tt) P (l e , s) (wp (l e) refl)
ASTSufficientPT.opSuf RWSSuf (RWStell out refl) f fSuf P i wp = wp
ASTSufficientPT.opSuf RWSSuf (RWSlisten refl) f fSuf P i wp =
  fSuf _ _ _ wp
ASTSufficientPT.opSuf RWSSuf RWSpass f fSuf P i wp =
  let ((x₁ , g) , s₁ , o₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift tt)) i
  in fSuf (Level.lift tt) (RWSpassPost P) i wp (g o₁) refl

private
  twoOuts : ∀ f i → TwoOuts (runRWS (prog₁ f) i)
  twoOuts f i = ASTSufficientPT.sufficient RWSSuf (prog₁ f) TwoOuts i (wpTwoOuts f i)
