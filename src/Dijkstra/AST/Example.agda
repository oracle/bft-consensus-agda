{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

module Dijkstra.AST.Example (Ev Wr St : Set) where

open import Data.Empty
open import Data.Fin
open import Data.List using ([_])
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Dijkstra.AST.Core
open import Function
open import Haskell.Prelude
  hiding (maybe)
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality
  hiding ([_])

data RWSCmd (A : Set) : Set₁ where
  RWSgets   : (g : St → A) → RWSCmd A
  RWStell   : (out : List Wr) → (A ≡ Unit) → RWSCmd A
  RWSpass   : RWSCmd A
  RWSmaybe  : ∀ {B} → Maybe B → RWSCmd A

RWSSubArg : {A : Set} (c : RWSCmd A) → Set₁
RWSSubArg (RWSgets g)         = Level.Lift _ Void
RWSSubArg (RWStell out refl)  = Level.Lift _ Void
RWSSubArg RWSpass             = Level.Lift _ Unit
RWSSubArg (RWSmaybe{B} x)     = Level.Lift _ (Maybe B)

RWSSubRet : {A : Set} {c : RWSCmd A} (r : RWSSubArg c) → Set
RWSSubRet{_} {RWSgets g} _ = Unit
RWSSubRet{A} {RWStell out x} _ = ⊥
RWSSubRet{A} {RWSpass} _ = A × (List Wr → List Wr)
RWSSubRet{A} {RWSmaybe x} _ = A

RWSOps : ASTOps
ASTOps.Cmd RWSOps     = RWSCmd
ASTOps.SubArg RWSOps  = RWSSubArg
ASTOps.SubRet RWSOps  = RWSSubRet

RWS = AST RWSOps

module Syntax where
  open import Dijkstra.AST.Syntax public

  gets : ∀ {A} → (St → A) → RWS A
  gets f = ASTop (RWSgets f) λ ()

  tell : List Wr → RWS Unit
  tell outs = ASTop (RWStell outs refl) (λ ())

  pass : ∀ {A} → RWS (A × (List Wr → List Wr)) → RWS A
  pass m = ASTop RWSpass (λ where (Level.lift unit) → m)

  maybe : ∀ {A B} → Maybe B → RWS A → (B → RWS A) → RWS A
  maybe m c₁ c₂ = ASTop (RWSmaybe m) λ where
    (Level.lift nothing)  → c₁
    (Level.lift (just x)) → c₂ x

private
  module Prog where
    module Raw where
      prog : (St → Maybe Wr) → RWS Unit
      prog f =
        ASTop RWSpass λ _ →
          ASTbind (ASTop (RWSgets f) λ ()) λ m →
          ASTop (RWSmaybe m) λ where
            (Level.lift nothing)  → ASTreturn (unit , λ x → x ++ x)
            (Level.lift (just w)) →
              ASTbind (ASTop (RWStell ([ w ]) refl) (λ ())) λ _ →
              ASTreturn (unit , λ _ → [])

    module Sugar where
      open Syntax
      prog : (St → Maybe Wr) → RWS Unit
      prog f =
        pass $ do
          m ← gets f
          maybe m (return (unit , λ x → x ++ x))
            λ w → do
              tell [ w ]
              return (unit , λ _ → [])

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
ASTOpSem.runAST RWSOpSem (ASTop (RWStell out refl) f) (ev , st) =
  unit , st , out
ASTOpSem.runAST RWSOpSem (ASTop RWSpass f) (ev , st) =
  let ((x₁ , wf) , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) (ev , st)
  in x₁ , st₁ , wf outs₁
ASTOpSem.runAST RWSOpSem (ASTop (RWSmaybe m) f) (ev , st) =
  ASTOpSem.runAST RWSOpSem (f (Level.lift m)) (ev , st)

runRWS = ASTOpSem.runAST RWSOpSem

RWSbindPost : (outs : List Wr) {A : Set} → Post A → Post A
RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

RWSpassPost : ∀ {A} → Post A → Post (A × (List Wr → List Wr))
RWSpassPost P ((x , f) , s , o) = ∀ o' → o' ≡ f o → P (x , s , o')

RWSPredTrans : ASTPredTrans RWSOps RWSTypes
ASTPredTrans.returnPT RWSPredTrans x P (ev , st) =
  P (x , st , [])
ASTPredTrans.bindPT RWSPredTrans f (ev , st) P (x , st' , outs) =
  ∀ r → r ≡ x → f r (RWSbindPost outs P) (ev , st')
ASTPredTrans.opPT RWSPredTrans (RWSgets g) f P (ev , st) =
  P (g st , st , [])
ASTPredTrans.opPT RWSPredTrans (RWStell out refl) f P (ev , st) =
  P (unit , st , out)
ASTPredTrans.opPT RWSPredTrans{A} RWSpass f P (ev , st) =
  f (Level.lift unit) (RWSpassPost P) (ev , st)
ASTPredTrans.opPT RWSPredTrans{A} (RWSmaybe m) f P (ev , st) =
    (nothing ≡ m → f (Level.lift nothing) P (ev , st))
  × (∀ x → just x ≡ m → f (Level.lift (just x)) P (ev , st))

RWSPT = ASTPredTrans.predTrans RWSPredTrans

private
  module ProgPost where
    open Prog.Sugar
    ProgPost : Input → Post Unit
    ProgPost (_ , s1) (_ , s2 , o) = s1 ≡ s2 × length o ≡ 0

    -- TODO-1: finish holes in wpProgPost
    wpProgPost : ∀ f i → RWSPT (prog f) (ProgPost i) i
    proj₁ (wpProgPost f i m mEq) _ o refl = refl , {!!}
    proj₂ (wpProgPost f i m mEq) = {!!}
    -- proj₁ (wpProgPost f i m mEq) refl [] refl = refl , refl
    -- proj₂ (wpProgPost f i m mEq) x refl _ _ [] refl = refl , refl
{-
Goal: (r : Maybe Wr) →
      r ≡ f (proj₂ i) →
      (nothing ≡ r →
       RWSbindPost [] (RWSpassPost (ProgPost i))
       ((unit , (λ x → x ++ x)) , proj₂ i , []))
      ×
      ((x : Wr) →
       just x ≡ r →
       (r₁ : Unit) →
       r₁ ≡ unit →
       RWSbindPost (x ∷ []) (RWSbindPost [] (RWSpassPost (ProgPost i)))
       ((unit , (λ _ → [])) , proj₂ i , []))
————————————————————————————————————————————————————————————
i  : Input
f  : St → Maybe Wr
St : Set
Wr : Set
Ev : Set
-}

    -- TODO-1: finish holes in progPost'
    progPost' : ∀ f i → ProgPost i (runRWS (prog f) i)
    progPost' f (e , s) = {!!}
{-
Goal: Data.Product.Σ
      (s ≡
       proj₁
       (proj₂
        (ASTOpSem.runAST RWSOpSem
         ((λ { (Level.lift nothing) → ASTreturn (unit , (λ x → x ++ x))
             ; (Level.lift (just x))
                 → ASTbind (ASTop (RWStell (x ∷ []) refl) (λ ()))
                   (λ _ → ASTreturn (unit , (λ _ → [])))
             })
          (Level.lift (f s)))
         (e , s))))
      (λ x →
         foldr (λ _ → Agda.Builtin.Nat.Nat.suc) 0
         (proj₂
          (proj₁
           (ASTOpSem.runAST RWSOpSem
            ((λ { (Level.lift nothing) → ASTreturn (unit , (λ x₁ → x₁ ++ x₁))
                ; (Level.lift (just x))
                    → ASTbind (ASTop (RWStell (x ∷ []) refl) (λ ()))
                      (λ _ → ASTreturn (unit , (λ _ → [])))
                })
             (Level.lift (f s)))
            (e , s)))
          (proj₂
           (proj₂
            (ASTOpSem.runAST RWSOpSem
             ((λ { (Level.lift nothing) → ASTreturn (unit , (λ x₁ → x₁ ++ x₁))
                 ; (Level.lift (just x))
                     → ASTbind (ASTop (RWStell (x ∷ []) refl) (λ ()))
                       (λ _ → ASTreturn (unit , (λ _ → [])))
                 })
              (Level.lift (f s)))
             (e , s)))))
         ≡ 0)
-}
-- 34 lines...
    --   with f s
    -- ... | nothing = refl , refl
    -- ... | just x  = refl , refl


  -- wpTwoOuts : ∀ f i → ASTPredTrans.predTrans RWSPT (prog₁ f) TwoOuts i
  -- wpTwoOuts f (e , s) w w= unit refl .(w ∷ w ∷ []) refl = refl

-- RWSPTMono : ASTPredTransMono RWSPT
-- ASTPredTransMono.returnPTMono RWSPTMono x P₁ P₂ P₁⊆ₒP₂ i wp =
--   P₁⊆ₒP₂ _ wp
-- ASTPredTransMono.bindPTMono₁ RWSPTMono f monoF (ev , st) P₁ P₂ P₁⊆ₒP₂ (x₁ , st₁ , outs₁) wp .x₁ refl =
--   monoF _ _ _ (λ o' pf' → P₁⊆ₒP₂ _ pf') (ev , st₁) (wp _ refl)
-- ASTPredTransMono.bindPTMono₂ RWSPTMono f₁ f₂ f₁⊑f₂ (ev , st) P (x₁ , st₁ , outs₁) wp .x₁ refl =
--   f₁⊑f₂ x₁ (RWSbindPost outs₁ P) (ev , st₁) (wp x₁ refl)
-- ASTPredTransMono.opPTMono₁ RWSPTMono (RWSgets g) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
--   P₁⊆ₒP₂ _ wp
-- ASTPredTransMono.opPTMono₁ RWSPTMono (RWSask refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
--   P₁⊆ₒP₂ _ wp
-- ASTPredTransMono.opPTMono₁ RWSPTMono (RWStell out refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
--   P₁⊆ₒP₂ _ wp
-- ASTPredTransMono.opPTMono₁ RWSPTMono RWSpass f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
--   monoF (Level.lift unit) _ _ (λ where ((x' , w') , st' , o') pf₁ ._ refl → P₁⊆ₒP₂ _ (pf₁ _ refl)) (ev , st) wp
-- proj₁ (ASTPredTransMono.opPTMono₁ RWSPTMono (RWSif c) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp) refl =
--   monoF (Level.lift true) _ _ P₁⊆ₒP₂ _ (proj₁ wp refl)
-- proj₂ (ASTPredTransMono.opPTMono₁ RWSPTMono (RWSif c) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp) refl =
--   monoF (Level.lift false) _ _ P₁⊆ₒP₂ _ (proj₂ wp refl)
-- ASTPredTransMono.opPTMono₂ RWSPTMono (RWSgets g) f₁ f₂ f₁⊑f₂ P i wp =
--   wp
-- ASTPredTransMono.opPTMono₂ RWSPTMono (RWSask refl) f₁ f₂ f₁⊑f₂ P i wp =
--   wp
-- ASTPredTransMono.opPTMono₂ RWSPTMono (RWStell out refl) f₁ f₂ f₁⊑f₂ P i wp =
--   wp
-- ASTPredTransMono.opPTMono₂ RWSPTMono RWSpass f₁ f₂ f₁⊑f₂ P i wp =
--   f₁⊑f₂ _ _ _ wp
-- proj₁ (ASTPredTransMono.opPTMono₂ RWSPTMono (RWSif c) f₁ f₂ f₁⊑f₂ P i wp) refl =
--   f₁⊑f₂ (Level.lift true) _ _ (proj₁ wp refl)
-- proj₂ (ASTPredTransMono.opPTMono₂ RWSPTMono (RWSif c) f₁ f₂ f₁⊑f₂ P i wp) refl =
--   f₁⊑f₂ (Level.lift false) _ _ (proj₂ wp refl )

-- RWSSuf : ASTSufficientPT RWSOpSem RWSPT
-- ASTSufficientPT.returnSuf RWSSuf x P i wp = wp
-- ASTSufficientPT.bindSuf RWSSuf m f mSuf fSuf P (e , s₀) wp =
--   let (x₁ , s₁ , o₁) = ASTOpSem.runAST RWSOpSem m (e , s₀)
--       wpₘ = mSuf _ (e , s₀) wp _ refl
--   in fSuf x₁ _ (e , s₁) wpₘ
-- ASTSufficientPT.opSuf RWSSuf (RWSgets g) f fSuf P i wp = wp
-- ASTSufficientPT.opSuf RWSSuf (RWSask refl) f fSuf P i wp = wp
-- ASTSufficientPT.opSuf RWSSuf (RWStell out refl) f fSuf P i wp = wp
-- ASTSufficientPT.opSuf RWSSuf RWSpass f fSuf P i wp =
--   let ((x₁ , g) , s₁ , o₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) i
--   in fSuf (Level.lift unit) (RWSpassPost P) i wp (g o₁) refl
-- ASTSufficientPT.opSuf RWSSuf (RWSif false) f fSuf P i wp =
--   fSuf (Level.lift false) _ _ (proj₂ wp refl)
-- ASTSufficientPT.opSuf RWSSuf (RWSif true) f fSuf P i wp =
--   fSuf (Level.lift true) _ _ (proj₁ wp refl)

-- private
--   twoOuts : ∀ f i → TwoOuts (runRWS (prog₁ f) i)
--   twoOuts f i = ASTSufficientPT.sufficient RWSSuf (prog₁ f) TwoOuts i (wpTwoOuts f i)
