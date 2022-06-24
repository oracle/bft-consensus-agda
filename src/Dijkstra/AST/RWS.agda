{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.RWS (Ev Wr St : Set) where

open import Data.Empty
open import Data.Fin hiding (lift)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Function
open import Haskell.Prelude
open import Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

module RWSBase where

  open import Dijkstra.AST.Core

  data RWSCmd (A : Set) : Set₁ where
    RWSgets   : (g : St → A)                      → RWSCmd A
    RWSputs   : (p : St → St) → (A ≡ Unit)        → RWSCmd A
    RWSask    : (A ≡ Ev)                          → RWSCmd A
    RWSlocal  : (l : Ev → Ev)                     → RWSCmd A
    RWStell   : (outs : List Wr) → (A ≡ Unit)     → RWSCmd A
    RWSlisten : {A' : Set} → (A ≡ (A' × List Wr)) → RWSCmd A
    RWSpass   :                                     RWSCmd A


  RWSSubArg : {A : Set} (c : RWSCmd A) → Set₁
  RWSSubArg (RWSgets g)          = Lift _ Void
  RWSSubArg (RWSputs p refl)     = Lift _ Void
  RWSSubArg (RWSask refl)        = Lift _ Void
  RWSSubArg (RWSlocal l)         = Lift _ Unit
  RWSSubArg (RWStell out refl)   = Lift _ Void
  RWSSubArg (RWSlisten{A'} refl) = Lift _ Unit
  RWSSubArg  RWSpass             = Lift _ Unit

  RWSSubRet : {A : Set} {c : RWSCmd A} (r : RWSSubArg c) → Set
  RWSSubRet {_}              {RWSgets g}          (lift ())
  RWSSubRet {_}              {RWSputs p refl}     (lift ())
  RWSSubRet {_}              {RWSask refl}        (lift ())
  RWSSubRet {A}              {RWSlocal l}         _         = A
  RWSSubRet {_}              {RWStell out refl}   (lift ())
  RWSSubRet {.(_ × List Wr)} {RWSlisten{A'} refl} _         = A'
  RWSSubRet {A}              {RWSpass}            _         = A × (List Wr → List Wr)

  open ASTOps
  RWSOps : ASTOps
  Cmd    RWSOps = RWSCmd
  SubArg RWSOps = RWSSubArg
  SubRet RWSOps = RWSSubRet

  RWSBaseAST = AST RWSOps

  module _ where
    open ASTTypes
    RWSTypes : ASTTypes
    Input  RWSTypes    = Ev × St
    Output RWSTypes A  = A × St × List Wr

  open ASTTypes RWSTypes

  module _ where
    open ASTOpSem
    RWSOpSem : ASTOpSem RWSOps RWSTypes
    runAST RWSOpSem (ASTreturn x) (ev , st) = x , st , []
    runAST RWSOpSem (ASTbind m f) (ev , st₀) =
      let (x₁ , st₁ , outs₁) = runAST RWSOpSem m (ev , st₀)
          (x₂ , st₂ , outs₂) = runAST RWSOpSem (f x₁) (ev , st₁)
      in (x₂ , st₂ , outs₁ ++ outs₂)
    runAST RWSOpSem (ASTop (RWSgets g)        f) (ev , st) =
      g st , st , []
    runAST RWSOpSem (ASTop (RWSputs p refl)   f) (ev , st) =
      unit , p st , []
    runAST RWSOpSem (ASTop (RWSask refl)      f) (ev , st) =
      ev , st , []
    runAST RWSOpSem (ASTop (RWSlocal l)       f) (ev , st) =
      runAST RWSOpSem (f (lift unit)) (l ev , st)
    runAST RWSOpSem (ASTop (RWStell out refl) f) (ev , st) =
      unit , st , out
    runAST RWSOpSem (ASTop (RWSlisten refl)   f) (ev , st) =
      let (x₁ , st₁ , outs₁) = runAST RWSOpSem (f (lift unit)) (ev , st)
      in (x₁ , outs₁) , st₁ , outs₁
    runAST RWSOpSem (ASTop RWSpass            f) (ev , st) =
      let ((x₁ , wf) , st₁ , outs₁) = runAST RWSOpSem (f (lift unit)) (ev , st)
      in x₁ , st₁ , wf outs₁

    runRWSBase = runAST RWSOpSem

  RWSbindPost : (outs : List Wr) {A : Set} → Post A → Post A
  RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

  RWSpassPost : ∀ {A} → Post A → Post (A × (List Wr → List Wr))
  RWSpassPost P ((x , f) , s , o) = ∀ o' → o' ≡ f o → P (x , s , o')

  RWSlistenPost : ∀ {A} → Post (A × List Wr) → Post A
  RWSlistenPost P (x , s , o) = P ((x , o) , s , o)

  open ASTPredTrans
  RWSPT : ASTPredTrans RWSOps RWSTypes
  returnPT RWSPT x P (ev , st) =
    P (x , st , [])
  bindPT   RWSPT f (ev , st) P (x , st' , outs) =
    ∀ r → r ≡ x → f r (RWSbindPost outs P) (ev , st')
  opPT     RWSPT (RWSgets g)          f P (ev , st) =
    P (g st , st , [])
  opPT     RWSPT (RWSputs p refl)     f P (ev , st) =
    P (unit , p st , [])
  opPT     RWSPT (RWSask refl)        f P (ev , st) =
    P (ev , st , [])
  opPT     RWSPT (RWSlocal l)         f P (ev , st) =
    ∀ ev' → ev' ≡ l ev → f (lift unit) P (ev' , st)
  opPT     RWSPT (RWStell out refl)   f P (ev , st) =
    P (unit , st , out)
  opPT     RWSPT (RWSlisten{A'} refl) f P (ev , st) =
    f (lift unit) (RWSlistenPost P) (ev , st)
  opPT     RWSPT{A} RWSpass           f P (ev , st) =
    f (lift unit) (RWSpassPost P) (ev , st)

  ------------------------------------------------------------------------------
  open ASTPredTransMono
  RWSPTMono : ASTPredTransMono RWSPT

  returnPTMono RWSPTMono                    x                                 P₁ P₂           P₁⊆P₂ i                  wp =
    P₁⊆P₂ _ wp
  bindPTMono   RWSPTMono                    f₁ f₂ mono₁ mono₂ f₁⊑f₂ (ev , st) P₁ P₂           P₁⊆P₂ (x₁ , st₁ , outs₁) wp r refl =
    f₁⊑f₂ x₁ _ (ev , st₁) (mono₁ x₁ _ _ (λ o' → P₁⊆P₂ _) (ev , st₁) (wp _ refl))
  opPTMono     RWSPTMono (RWSgets g)        f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    P₁⊆P₂ _ wp
  opPTMono     RWSPTMono (RWSputs p refl)   f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    P₁⊆P₂ _ wp
  opPTMono     RWSPTMono (RWSask refl)      f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    P₁⊆P₂ _ wp
  opPTMono     RWSPTMono (RWSlocal l)       f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp ev' refl =
    f₁⊑f₂ (lift unit) _ _ (mono₁ (lift unit) _ _ P₁⊆P₂ _ (wp _ refl))
  opPTMono     RWSPTMono (RWStell out refl) f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    P₁⊆P₂ _ wp
  opPTMono     RWSPTMono (RWSlisten refl)   f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    f₁⊑f₂ (lift unit) _ _ (mono₁ (lift unit) _ _ (λ where (x' , st' , o') → P₁⊆P₂ _) _ wp)
  opPTMono     RWSPTMono RWSpass            f₁ f₂ mono₁ mono₂ f₁⊑f₂           P₁ P₂ (ev , st) P₁⊆P₂                    wp =
    f₁⊑f₂ (lift unit) _ _ (mono₁ (lift unit) _ _ (λ where ((x' , w') , st' , o') pf₁ _ refl → P₁⊆P₂ _ (pf₁ _ refl)) _ wp)

  ------------------------------------------------------------------------------
  open ASTOpSem RWSOpSem
  open ASTSufficientPT
  RWSSuf : ASTSufficientPT RWSOpSem RWSPT

  returnSuf RWSSuf x P i wp = wp
  bindSuf   RWSSuf m f mSuf fSuf P (e , s₀) wp =
    let (x₁ , s₁ , o₁) = runAST m (e , s₀)
        wpₘ = mSuf _ (e , s₀) wp _ refl
    in fSuf x₁ _ (e , s₁) wpₘ
  opSuf     RWSSuf (RWSgets g)        f fSuf P _       wp = wp
  opSuf     RWSSuf (RWSputs p refl)   f fSuf P _       wp = wp
  opSuf     RWSSuf (RWSask refl)      f fSuf P _       wp = wp
  opSuf     RWSSuf (RWSlocal l)       f fSuf P (e , s) wp =
       fSuf _ _ (l e , s) (wp (l e) refl)
  opSuf     RWSSuf (RWStell out refl) f fSuf P _       wp = wp
  opSuf     RWSSuf (RWSlisten refl)   f fSuf P _       wp =
       fSuf _ _ _          wp
  opSuf     RWSSuf RWSpass            f fSuf P i       wp =
    let ((x₁ , g) , s₁ , o₁) = runAST (f (lift unit)) i
    in fSuf _ _ _          wp (g o₁) refl

  open ASTNecessaryPT
  RWSNec : ASTNecessaryPT RWSOpSem RWSPT
  returnNec RWSNec x P _                              = id
  bindNec   RWSNec {A} {B} m f mNec fNec P (e , s) Pr
    with runAST m (e , s) | inspect (runAST m) (e , s)
  ... | r , s' , wr | [ refl ]                        =
    mNec _ (e , s) λ where _ refl → fNec r (RWSbindPost wr P) (e , s') Pr
  opNec RWSNec (RWSgets g)           f fNec P _       = id
  opNec RWSNec (RWSputs p refl)      f fNec P _       = id
  opNec RWSNec (RWSask refl)         f fNec P _       = id
  opNec RWSNec (RWSlocal l)          f fNec P (e , s) =
    λ where Pr ev' refl → fNec (lift _) _ (ev' , s)                    Pr
  opNec RWSNec (RWStell outs refl)   f fNec P _       = id
  opNec RWSNec (RWSlisten {A'} refl) f fNec P         = fNec (lift _) _
  opNec RWSNec  RWSpass              f fNec P _       =
    λ       Pr          → fNec (lift _) _ _         λ where o' refl →  Pr

module RWSAST where
  open RWSBase
  open RWSBase using (RWSbindPost ; RWSpassPost ; RWSlistenPost)    public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open ConditionalExtensions RWSPT RWSOpSem RWSPTMono RWSSuf RWSNec public

  RWSAST    = ExtAST

  runRWSAST = runAST

  module RWSSyntax where
    gets : ∀ {A} → (St → A) → RWSAST A
    gets g = ASTop (Left (RWSgets g)) λ ()

    puts : (St → St) → RWSAST Unit
    puts p = ASTop (Left (RWSputs p refl)) (λ ())

    ask : RWSAST Ev
    ask = ASTop (Left (RWSask refl)) (λ ())

    local : ∀ {A} → (Ev → Ev) → RWSAST A → RWSAST A
    local l m = ASTop (Left (RWSlocal l)) (λ where (lift unit) → m)

    tell : List Wr → RWSAST Unit
    tell outs = ASTop (Left (RWStell outs refl)) (λ ())

    listen : ∀ {A} → RWSAST A → RWSAST (A × List Wr)
    listen m = ASTop (Left (RWSlisten refl)) λ where (lift unit) → m

    pass : ∀ {A} → RWSAST (A × (List Wr → List Wr)) → RWSAST A
    pass m = ASTop (Left RWSpass) (λ where (lift unit) → m)

open RWSAST    public
open RWSSyntax public

module RWSExample where
  open RWSAST
  open RWSSyntax

  module _ where
    open import Dijkstra.AST.Core
    open        RWSBase

    prog₁ : (St → Wr) → RWSAST Unit
    prog₁ g =
      ASTop (Left RWSpass) λ _ →
        ASTbind (ASTop (Left (RWSgets g)) λ ()) λ w →
        ASTbind (ASTop (Left (RWStell (w ∷ []) refl)) λ ()) λ _ →
        ASTreturn (unit , λ o → o ++ o)

  prog₁' : (St → Wr) → RWSAST Unit
  prog₁' g =
    pass $ do
      w ← gets g
      tell (w ∷ [])
      return (unit , λ o → o ++ o)

  TwoOuts : Post Unit
  TwoOuts (_ , _ , o) = length o ≡ 2

  wpTwoOuts : ∀ g i → predTrans (prog₁ g) TwoOuts i
  wpTwoOuts g (e , s) w w= unit refl .(w ∷ w ∷ []) refl = refl

  twoOuts : ∀ g i → TwoOuts (runRWSAST (prog₁ g) i)
  twoOuts g i = sufficient (prog₁ g) TwoOuts i (wpTwoOuts g i)
