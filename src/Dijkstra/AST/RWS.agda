{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.RWS (Ev Wr St : Set) where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality
  hiding ([_])

module RWSBase where

  open import Dijkstra.AST.Core

  data RWSCmd (A : Set) : Set₁ where
    RWSgets   : (g : St → A)                      → RWSCmd A
    RWSputs   : (p : St → St) → (A ≡ Unit)        → RWSCmd A
    RWSask    : (A ≡ Ev)                          → RWSCmd A
    RWSlocal  : (l : Ev → Ev)                     → RWSCmd A
    RWStell   : (out : List Wr) → (A ≡ Unit)      → RWSCmd A
    RWSlisten : {A' : Set} → (A ≡ (A' × List Wr)) → RWSCmd A
    RWSpass   :                                     RWSCmd A


  RWSSubArg : {A : Set} (c : RWSCmd A) → Set₁
  RWSSubArg (RWSgets g)          = Level.Lift _ Void
  RWSSubArg (RWSputs p refl)     = Level.Lift _ Void
  RWSSubArg (RWSask refl)        = Level.Lift _ Void
  RWSSubArg (RWSlocal l)         = Level.Lift _ Unit
  RWSSubArg (RWStell out refl)   = Level.Lift _ Void
  RWSSubArg (RWSlisten{A'} refl) = Level.Lift _ Unit
  RWSSubArg  RWSpass             = Level.Lift _ Unit

  RWSSubRet : {A : Set} {c : RWSCmd A} (r : RWSSubArg c) → Set
  RWSSubRet {_}              {RWSgets g} _          = Void
  RWSSubRet {_}              {RWSputs p x} _        = Void
  RWSSubRet {_}              {RWSask x} _           = Void
  RWSSubRet {A}              {RWSlocal l} _         = A
  RWSSubRet {_}              {RWStell out x} _      = Void
  RWSSubRet {.(_ × List Wr)} {RWSlisten{A'} refl} _ = A'
  RWSSubRet {A}              {RWSpass} _            = A × (List Wr → List Wr)

  RWSOps : ASTOps
  ASTOps.Cmd RWSOps     = RWSCmd
  ASTOps.SubArg RWSOps  = RWSSubArg
  ASTOps.SubRet RWSOps  = RWSSubRet

  RWSBaseAST = AST RWSOps

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
  ASTOpSem.runAST RWSOpSem (ASTop (RWSgets g)        f) (ev , st) =
    g st , st , []
  ASTOpSem.runAST RWSOpSem (ASTop (RWSputs p refl)   f) (ev , st) =
    unit , p st , []
  ASTOpSem.runAST RWSOpSem (ASTop (RWSask refl)      f) (ev , st) =
    ev , st , []
  ASTOpSem.runAST RWSOpSem (ASTop (RWSlocal l)       f) (ev , st) =
    ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) (l ev , st)
  ASTOpSem.runAST RWSOpSem (ASTop (RWStell out refl) f) (ev , st) =
    unit , st , out
  ASTOpSem.runAST RWSOpSem (ASTop (RWSlisten refl)   f) (ev , st) =
    let (x₁ , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) (ev , st)
    in (x₁ , outs₁) , st₁ , outs₁
  ASTOpSem.runAST RWSOpSem (ASTop RWSpass            f) (ev , st) =
    let ((x₁ , wf) , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) (ev , st)
    in x₁ , st₁ , wf outs₁

  runRWSBase = ASTOpSem.runAST RWSOpSem

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
    ∀ ev' → ev' ≡ l ev → f (Level.lift unit) P (ev' , st)
  ASTPredTrans.opPT RWSPT (RWStell out refl) f P (ev , st) =
    P (unit , st , out)
  ASTPredTrans.opPT RWSPT (RWSlisten{A'} refl) f P (ev , st) =
    f (Level.lift unit) (RWSlistenPost P) (ev , st)
  ASTPredTrans.opPT RWSPT{A} RWSpass f P (ev , st) =
    f (Level.lift unit) (RWSpassPost P) (ev , st)

  open ASTPredTrans RWSPT
  open ASTPTWeakest RWSOpSem RWSPT

  predTrans-is-weakest-base : ∀ {ev : Ev}{st : St}{A} → (m : RWSBaseAST A) → Post⇒wp-base {A} m (ev , st)
  predTrans-is-weakest-base           (ASTreturn _) _ = id
  predTrans-is-weakest-base {ev} {st} (ASTbind m f) _ Pr
     with predTrans-is-weakest-base {ev} {st} m
  ...| rec
    with runRWSBase m (ev , st)
  ... | r , st' , wr = rec _ λ where _ refl → predTrans-is-weakest-base (f r) _ Pr
  predTrans-is-weakest-base              (ASTop (RWSgets g)                      f) P    = id
  predTrans-is-weakest-base              (ASTop (RWSputs p refl)                 f) P    = id
  predTrans-is-weakest-base              (ASTop (RWSask    refl)                 f) P    = id
  predTrans-is-weakest-base {ev} {st}    (ASTop (RWSlocal l)                     f) P Pr =
    λ where _ refl → predTrans-is-weakest-base {l ev} {st} (f (Level.lift unit)) _ Pr
  predTrans-is-weakest-base              (ASTop (RWStell out refl)               f) P    = id
  predTrans-is-weakest-base {ev} {st}    (ASTop (RWSlisten {A'} refl)            f) P Pr =
    predTrans-is-weakest-base {ev} {st} {A'} (f (Level.lift unit)) _ Pr
  predTrans-is-weakest-base {ev} {st} {A} (ASTop RWSpass                         f) P Pr =
    predTrans-is-weakest-base {ev} {st}      (f (Level.lift unit)) _ λ where _ refl → Pr

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
    monoF (Level.lift unit) _ _ P₁⊆ₒP₂ (l ev , st) (wp _ refl)
  ASTPredTransMono.opPTMono₁ RWSPTMono (RWStell out refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
    P₁⊆ₒP₂ _ wp
  ASTPredTransMono.opPTMono₁ RWSPTMono (RWSlisten refl) f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
    monoF (Level.lift unit) _ _ (λ where (x' , st' , o') → P₁⊆ₒP₂ _) (ev , st) wp
  ASTPredTransMono.opPTMono₁ RWSPTMono RWSpass f monoF P₁ P₂ P₁⊆ₒP₂ (ev , st) wp =
    monoF (Level.lift unit) _ _ (λ where ((x' , w') , st' , o') pf₁ ._ refl → P₁⊆ₒP₂ _ (pf₁ _ refl)) (ev , st) wp
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWSgets g) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWSputs p refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWSask refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWSlocal l) f₁ f₂ f₁⊑f₂ P (ev , st) wp .(l ev) refl =
    f₁⊑f₂ (Level.lift unit) _ _ (wp _ refl)
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWStell out refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ RWSPTMono (RWSlisten refl) f₁ f₂ f₁⊑f₂ P i wp =
    f₁⊑f₂ (Level.lift unit) _ _ wp
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
    fSuf (Level.lift unit) P (l e , s) (wp (l e) refl)
  ASTSufficientPT.opSuf RWSSuf (RWStell out refl) f fSuf P i wp = wp
  ASTSufficientPT.opSuf RWSSuf (RWSlisten refl) f fSuf P i wp =
    fSuf _ _ _ wp
  ASTSufficientPT.opSuf RWSSuf RWSpass f fSuf P i wp =
    let ((x₁ , g) , s₁ , o₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift unit)) i
    in fSuf (Level.lift unit) (RWSpassPost P) i wp (g o₁) refl

module RWSAST where
  open RWSBase
  open RWSBase using (RWSbindPost ; RWSpassPost ; RWSlistenPost) public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open ConditionalExtensions RWSPT RWSOpSem RWSPTMono RWSSuf     public
  open WithPTIWBase predTrans-is-weakest-base                    public

  RWSAST    = ExtAST

  runRWSAST = runAST


  module RWSSyntax where
    gets : ∀ {A} → (St → A) → RWSAST A
    gets f = ASTop (Left (RWSgets f)) λ ()

    puts : (St → St) → RWSAST Unit
    puts f = ASTop (Left (RWSputs f refl)) (λ ())

    ask : RWSAST Ev
    ask = ASTop (Left (RWSask refl)) (λ ())

    local : ∀ {A} → (Ev → Ev) → RWSAST A → RWSAST A
    local f m = ASTop (Left (RWSlocal f)) (λ where (Level.lift unit) → m)

    tell : List Wr → RWSAST Unit
    tell outs = ASTop (Left (RWStell outs refl)) (λ ())

    listen : ∀ {A} → RWSAST A → RWSAST (A × List Wr)
    listen m = ASTop (Left (RWSlisten refl)) λ where (Level.lift unit) → m

    pass : ∀ {A} → RWSAST (A × (List Wr → List Wr)) → RWSAST A
    pass m = ASTop (Left RWSpass) (λ where (Level.lift unit) → m)

open RWSAST    public
open RWSSyntax public

module RWSExample where
  open RWSAST
  open RWSSyntax

  module _ where
    open import Dijkstra.AST.Core
    open        RWSBase

    prog₁ : (St → Wr) → RWSAST Unit
    prog₁ f =
      ASTop (Left RWSpass) λ _ →
        ASTbind (ASTop (Left (RWSgets f)) λ ()) λ w →
        ASTbind (ASTop (Left (RWStell (w ∷ []) refl)) λ ()) λ _ →
        ASTreturn (unit , λ o → o ++ o)

  prog₁' : (St → Wr) → RWSAST Unit
  prog₁' f =
    pass $ do
      w ← gets f
      tell (w ∷ [])
      return (unit , λ o → o ++ o)

  TwoOuts : Post Unit
  TwoOuts (_ , _ , o) = length o ≡ 2

  wpTwoOuts : ∀ f i → predTrans (prog₁ f) TwoOuts i
  wpTwoOuts f (e , s) w w= unit refl .(w ∷ w ∷ []) refl = refl

  twoOuts : ∀ f i → TwoOuts (runRWSAST (prog₁ f) i)
  twoOuts f i = sufficient (prog₁ f) TwoOuts i (wpTwoOuts f i)

