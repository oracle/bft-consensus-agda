{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

data AST
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set → Set₁ where
  -- monadic operations
  ASTreturn : ∀ {A} → A → AST C R A
  ASTbind   : ∀ {A B} → (m : AST C R A) (f : A → AST C R B)
              → AST C R B
  -- effect operations
  ASTop : ∀ {A} → (c : C A) (f : R A c → AST C R A) → AST C R A

record ASTTypes : Set₁ where
  constructor mkASTTypes
  field
    Input  : Set
    Output : (A : Set) → Set

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

record ASTImpl
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₁ where
  constructor mkASTImpl
  field
    M : Set → Set
    runAST : ∀ {A} → AST C R A → M A

record MonadASTImpl
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (M : Set → Set): Set₁ where
  field
    ret : ∀ {A} → A → M A
    bind   : ∀ {A B} → (m : M A) (f : A → M B) → M B
    op     : ∀ {A}  → (c : C A) (f : R A c → M A) → M A

  impl : ASTImpl C R
  ASTImpl.M impl = M
  ASTImpl.runAST impl (ASTreturn x) = ret x
  ASTImpl.runAST impl (ASTbind x f) = bind (ASTImpl.runAST impl x) (ASTImpl.runAST impl ∘ f)
  ASTImpl.runAST impl (ASTop c f) = op c (ASTImpl.runAST impl ∘ f)
open MonadASTImpl ⦃ ... ⦄ public
  hiding (impl)

record ASTOpSem
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (Types : ASTTypes) : Set₁ where
  constructor mkASTOpSem
  open ASTTypes Types
  field
    impl : ASTImpl C R
  open ASTImpl impl public
  field
    runM : ∀ {A} → M A → Input → Output A

module SimpleASTOpSem
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (Types : ASTTypes)
  (monadOp : MonadASTImpl C R λ A → ASTTypes.Input Types → ASTTypes.Output Types A) where

  OS : ASTOpSem C R Types
  ASTOpSem.impl OS = MonadASTImpl.impl monadOp
  ASTOpSem.runM OS = id

record ASTPredTrans
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (Types : ASTTypes) : Set₂ where
  constructor mkASTPredTrans
  open ASTTypes Types
  field
    returnPT : ∀ {A} → A → PredTrans A
    bindPT   : ∀ {A B} → (f : A → PredTrans B) (i : Input)
                → (P : Post B) → Post A
    opPT     : ∀ {A} → (c : C A) → (R A c → PredTrans A) → PredTrans A

  predTrans : ∀ {A} → AST C R A → PredTrans A
  predTrans (ASTreturn x) P i =
    returnPT x P i
  predTrans (ASTbind x f) P i =
    predTrans x (bindPT (predTrans ∘ f) i P) i
  predTrans (ASTop c f) P i =
    opPT c (predTrans ∘ f) P i

record ASTPredTransMono
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (Types : ASTTypes) (PT : ASTPredTrans C R Types): Set₂ where
  open ASTTypes Types
  open ASTPredTrans PT
  field
    returnPTMono : ∀ {A} → (x : A) → MonoPredTrans (returnPT x)
    bindPTMono₁  : ∀ {A B} → (f : A → PredTrans B)
                   → (∀ x → MonoPredTrans (f x))
                   → ∀ i P₁ P₂ → P₁ ⊆ₒ P₂ → bindPT f i P₁ ⊆ₒ bindPT f i P₂
    bindPTMono₂  : ∀ {A B} → (f₁ f₂ : A → PredTrans B)
                   → (f₁⊑f₂ : ∀ x → f₁ x ⊑ f₂ x)
                   → ∀ i P → bindPT f₁ i  P ⊆ₒ bindPT f₂ i P
    opPTMono₁    : ∀ {A} (c : C A) (f : R A c → PredTrans A)
                   → (∀ r → MonoPredTrans (f r))
                   → ∀ P₁ P₂ → P₁ ⊆ₒ P₂ → opPT c f P₁ ⊆ᵢ opPT c f P₂
    opPTMono₂    : ∀ {A} (c : C A) (f₁ f₂ : R A c → PredTrans A)
                   → (f₁⊑f₂ : ∀ r → f₁ r ⊑ f₂ r)
                   → opPT c f₁ ⊑ opPT c f₂

  predTransMono : ∀ {A} (m : AST C R A)
                  → MonoPredTrans (predTrans m)
  predTransMono (ASTreturn x) =
    returnPTMono x
  predTransMono (ASTbind m f) P₁ P₂ P₁⊆P₂ i x₁ =
    predTransMono  m _ _
      (bindPTMono₁ (predTrans ∘ f) (predTransMono ∘ f) i _ _ P₁⊆P₂) i x₁
  predTransMono (ASTop c f) P₁ P₂ P₁⊆P₂ i wp =
    opPTMono₁ c (predTrans ∘ f) (predTransMono ∘ f) _ _ P₁⊆P₂ i wp

record ASTSufficientPT
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  (Types : ASTTypes)
  (os : ASTOpSem C R Types) (pt : ASTPredTrans C R Types) : Set₁ where
  constructor mkASTSufficientPT
  open ASTTypes Types
  open ASTOpSem     os
  open ASTPredTrans pt

  Sufficient : (A : Set) (m : AST C R A) → Set₁
  Sufficient A m =
    ∀ P i → (wp : predTrans m P i) → P (runM (runAST m) i)

  field
    returnSuf : ∀ {A} x → Sufficient A (ASTreturn x)
    bindSuf   : ∀ {A B} (m : AST C R A) (f : A → AST C R B)
                → (mSuf : Sufficient A m)
                → (fSuf : ∀ x → Sufficient B (f x))
                → Sufficient B (ASTbind m f)
    opSuf     : ∀ {A} → (c : C A) (f : R A c → AST C R A)
                → (∀ r → Sufficient A (f r))
                → Sufficient A (ASTop c f)

  sufficient : ∀ {A} → (m : AST C R A) → Sufficient A m
  sufficient (ASTreturn x) =
    returnSuf x
  sufficient (ASTbind m f) =
    bindSuf m f (sufficient m) (sufficient ∘ f)
  sufficient (ASTop c f) =
    opSuf c f (sufficient ∘ f)

module RWS (Ev Wr St : Set) where

  data C (A : Set) : Set₁ where
    RWSgets  : (g : St → A) → C A
    RWSputs  : (p : St → St) → A ≡ Unit → C A
    RWSask   : (A ≡ Ev) → C A
    RWSlocal : (l : Ev → Ev) → C A
    RWStell  : (outs : List Wr) → (A ≡ Unit) → C A

  R : (A : Set) (c : C A) → Set₁
  R A (RWSgets x) = Level.Lift _ ⊥
  R .Unit (RWSputs f refl) = Level.Lift _ ⊥
  R .Ev (RWSask refl) = Level.Lift _ ⊥
  R A (RWSlocal x) = Level.Lift _ ⊤
  R A (RWStell x refl) = Level.Lift _ ⊥

  RWS : Set → Set₁
  RWS = AST C R

  Types : ASTTypes
  ASTTypes.Input Types = Ev × St
  ASTTypes.Output Types A = A × St × List Wr

  open ASTTypes Types

  M : Set → Set
  M A = Input → Output A

  monadAST : MonadASTImpl C R M
  MonadASTImpl.ret monadAST x (ev , st) = x , st , []
  MonadASTImpl.bind monadAST m f i@(ev , st₀) =
    let (x₁ , st₁ , outs₁) = m i
        (x₂ , st₂ , outs₂) = f x₁ (ev , st₁)
    in  (x₂ , st₂ , outs₁ ++ outs₂)
  MonadASTImpl.op monadAST (RWSgets g) _ i@(ev , st) =
    g st , st , []
  MonadASTImpl.op monadAST (RWSputs p refl) _ i@(ev , st) =
    unit , p st , []
  MonadASTImpl.op monadAST (RWSask refl) _ i@(ev , st) =
    ev , st , []
  MonadASTImpl.op monadAST (RWSlocal l) f i@(ev , st) =
    f (Level.lift tt) (l ev , st)
  MonadASTImpl.op monadAST (RWStell outs refl) _ i@(ev , st) =
    unit , st , outs

  OS = SimpleASTOpSem.OS C R Types monadAST

  RWSPredTrans = ASTPredTrans C R Types

  RWSbindPost : List Wr → {A : Set} → Post A → Post A
  RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

  PT : RWSPredTrans
  ASTPredTrans.returnPT PT x P (ev , st) =
    P (x , st , [])
  ASTPredTrans.bindPT PT f (ev , stₒ) P (x , st₁ , outs₁) =
    ∀ r → r ≡ x → f r (RWSbindPost outs₁ P) (ev , st₁)
  ASTPredTrans.opPT PT (RWSgets g) f P (ev , pre) =
    P (g pre , pre , [])
  ASTPredTrans.opPT PT (RWSputs p refl) f P (ev , pre) =
    P (unit , p pre , [])
  ASTPredTrans.opPT PT (RWSask refl) f P (ev , pre) =
    P (ev , pre , [])
  ASTPredTrans.opPT PT (RWSlocal l) f P (ev , pre) =
    ∀ ev' → ev' ≡ l ev → f (Level.lift tt) P (ev' , pre)
  ASTPredTrans.opPT PT (RWStell outs refl) f P (ev , pre) =
    P (unit , pre , outs)

  Mono : ASTPredTransMono _ _ _ PT
  ASTPredTransMono.returnPTMono Mono x P₁ P₂ P₁⊆ₒP₂ i@(ev , st₀) wp =
    P₁⊆ₒP₂ (x , st₀ , []) wp
  ASTPredTransMono.bindPTMono₁ Mono f monoF i@(ev , st₀) P₁ P₂ P₁⊆P₂ (y , st₁ , outs₁) wp .y refl =
    monoF y
      (RWSbindPost outs₁ P₁) _
      (λ where (y' , st₁' , outs₁') pf → P₁⊆P₂ _ pf)
      (ev , st₁) (wp _ refl)
  ASTPredTransMono.bindPTMono₂ Mono f₁ f₂ f₁⊑f₂ (ev , _) P (x , st , outs) wp .x refl =
    f₁⊑f₂ x (RWSbindPost outs P) (ev , st) (wp _ refl)
  ASTPredTransMono.opPTMono₁ Mono (RWSgets g) f monoF P₁ P₂ P₁⊆P₂ (ev , st) wp =
    P₁⊆P₂ _ wp
  ASTPredTransMono.opPTMono₁ Mono (RWSputs p refl) f monoF P₁ P₂ P₁⊆P₂ (ev , st) wp =
    P₁⊆P₂ _ wp
  ASTPredTransMono.opPTMono₁ Mono (RWSask refl) f monoF P₁ P₂ P₁⊆P₂ (ev , st) wp =
    P₁⊆P₂ _ wp
  ASTPredTransMono.opPTMono₁ Mono (RWSlocal l) f monoF P₁ P₂ P₁⊆P₂ (ev , st) wp .(l ev) refl =
    monoF (Level.lift tt) _ _ P₁⊆P₂ (l ev , st) (wp _ refl)
  ASTPredTransMono.opPTMono₁ Mono (RWStell outs refl) f monoF P₁ P₂ P₁⊆P₂ (ev , st) wp =
    P₁⊆P₂ _ wp
  ASTPredTransMono.opPTMono₂ Mono (RWSgets g) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ Mono (RWSputs p refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ Mono (RWSask refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp
  ASTPredTransMono.opPTMono₂ Mono (RWSlocal l) f₁ f₂ f₁⊑f₂ P (ev , st) wp .(l ev) refl =
    f₁⊑f₂ (Level.lift tt) P (l ev , st) (wp _ refl)
  ASTPredTransMono.opPTMono₂ Mono (RWStell outs refl) f₁ f₂ f₁⊑f₂ P i wp =
    wp

  RWSSufficientPre =
    ASTSufficientPT C R Types OS PT

  SufPre : RWSSufficientPre
  ASTSufficientPT.returnSuf SufPre x P i wp = wp
  ASTSufficientPT.bindSuf SufPre m f mSuf fSuf P i@(ev , st₀) wp =
    let (x₁ , st₁ , outs₁) = ASTOpSem.runAST OS m i
        wp' = mSuf
                (ASTPredTrans.bindPT PT (ASTPredTrans.predTrans PT ∘ f)
                  i P)
                i wp
    in fSuf x₁ (RWSbindPost outs₁ P) (ev , st₁) (wp' x₁ refl)
  ASTSufficientPT.opSuf SufPre (RWSgets g) f ih P i@(ev , st₀) op₁ =
    op₁
  ASTSufficientPT.opSuf SufPre (RWSputs p refl) f ih P i@(ev , st₀) op₁ =
    op₁
  ASTSufficientPT.opSuf SufPre (RWSask refl) f ih P i@(ev , st₀) op₁ = op₁
  ASTSufficientPT.opSuf SufPre (RWSlocal l) f fSuf P i@(ev , st₀) op₁ =
    fSuf (Level.lift tt) P (l ev , st₀) (op₁ _ refl)
  ASTSufficientPT.opSuf SufPre (RWStell outs refl) f ih P i@(ev , st₀) op₁ =
    op₁

module Branching where
  data C (A : Set) : Set₁ where
    ASTif : Guards Unit → C A
    ASTeither : (A₁ A₂ : Set) → Either A₁ A₂ → C A
    ASTmaybe  : (A₁ : Set) → Maybe A₁ → C A

  R : (A : Set) (c : C A) → Set₁
  R A (ASTif gs) = Level.Lift _ (Fin (lengthGuards gs))
  R A (ASTeither A₁ A₂ _) = Level.Lift _ (Either A₁ A₂)
  R A (ASTmaybe A₁ _)     = Level.Lift _ (Maybe A₁)

module ErrASTBind (E : Set) where
  Cₘ = Unit

  Rₘ : Cₘ → Set → Set
  Rₘ _ = Either E 

module BranchExtend
  (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
  where

  CBranch : Set → Set₁
  CBranch A = Either (C A) (Branching.C A)

  RBranch : (A : Set) (c : CBranch A) → Set₁
  RBranch A (Left x) = R A x
  RBranch A (Right y) = Branching.R A y

  unextendGuards
    : ∀ {A} → (gs : Guards{b = Level.zero} Unit) (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → AST C R A)
      → AST C R A
  unextendGuards (otherwise≔ _) f = f (Level.lift zero)
  unextendGuards (clause (b ≔ c) gs) f =
    if (toBool b) then (f (Level.lift zero)) else
      (unextendGuards gs (λ where (Level.lift i) → f (Level.lift (suc i))))

  unextendBranch : ∀ {A} → AST CBranch RBranch A → AST C R A
  unextendBranch (ASTreturn x) = ASTreturn x
  unextendBranch (ASTbind x f) = ASTbind (unextendBranch x) (unextendBranch ∘ f)
  unextendBranch (ASTop (Left x) f) = ASTop x (unextendBranch ∘ f)
  unextendBranch (ASTop (Right (Branching.ASTif gs)) f) =
    unextendGuards gs (unextendBranch ∘ f)
  unextendBranch (ASTop (Right (Branching.ASTeither A₁ A₂ x)) f) =
    unextendBranch (f (Level.lift x))
  unextendBranch (ASTop (Right (Branching.ASTmaybe A₁ x)) f) =
    unextendBranch (f (Level.lift x))

  module OpSem (Types : ASTTypes) (OS : ASTOpSem C R Types) where

    OSBranch : ASTOpSem CBranch RBranch Types
    ASTImpl.M (ASTOpSem.impl OSBranch) =
      ASTImpl.M (ASTOpSem.impl OS)
    ASTImpl.runAST (ASTOpSem.impl OSBranch) x =
      ASTImpl.runAST (ASTOpSem.impl OS) (unextendBranch x)
    ASTOpSem.runM OSBranch = ASTOpSem.runM OS

  module PT (Types : ASTTypes) (PT : ASTPredTrans C R Types) where
    open ASTTypes Types

    PTGuards :
      ∀ {A} (P : Post A) (i : Input)
      → (gs : Guards{b = Level.# 0} Unit)
      → (pt : Level.Lift (Level.# 1) (Fin (lengthGuards gs))
              → PredTrans A)
      → Set
    PTGuards P i (otherwise≔ _) pt =
      pt (Level.lift Fin.zero) P i
    PTGuards P i (clause (b ≔ c) gs) pt =
      (toBool b ≡ true  → pt (Level.lift Fin.zero) P i)
      × (toBool b ≡ false → PTGuards P i gs (λ where (Level.lift i) → pt (Level.lift (suc i))))

    PTBranch : ASTPredTrans CBranch RBranch Types
    ASTPredTrans.returnPT PTBranch = ASTPredTrans.returnPT PT
    ASTPredTrans.bindPT PTBranch = ASTPredTrans.bindPT PT
    ASTPredTrans.opPT PTBranch (Left  l) x P i =
      ASTPredTrans.opPT PT l x P i
    ASTPredTrans.opPT PTBranch (Right (Branching.ASTif gs)) pt P i =
      PTGuards P i gs pt
    ASTPredTrans.opPT PTBranch (Right (Branching.ASTeither A₁ A₂ e)) pt P i =
        (∀ l → e ≡ Left  l → pt (Level.lift (Left l))  P i)
      × (∀ r → e ≡ Right r → pt (Level.lift (Right r)) P i)
    ASTPredTrans.opPT PTBranch (Right (Branching.ASTmaybe A₁ m)) pt P i =
        (m ≡ nothing → pt (Level.lift nothing) P i)
      × (∀ j → m ≡ just j → pt (Level.lift (just j)) P i)


    module _ (PTMono : ASTPredTransMono _ _ Types PT) where
      open ASTPredTrans
      open ASTPredTransMono PTMono

      monoPTBranch : ASTPredTransMono _ _ _ PTBranch
      ASTPredTransMono.returnPTMono monoPTBranch x P₁ P₂ P₁⊆P₂ i wp =
        returnPTMono x _ _ P₁⊆P₂ i wp
      ASTPredTransMono.bindPTMono₁ monoPTBranch f monoF i P₁ P₂ P₁⊆P₂ o wp =
        bindPTMono₁ f monoF i _ _ P₁⊆P₂ o wp
      ASTPredTransMono.bindPTMono₂ monoPTBranch f₁ f₂ f₁⊑f₂ i P o wp =
        bindPTMono₂ f₁ _ f₁⊑f₂ i P o wp
      ASTPredTransMono.opPTMono₁ monoPTBranch (Left x) f monoF P₁ P₂ P₁⊆P₂ i wp =
        opPTMono₁ x f monoF P₁ _ P₁⊆P₂ i wp
      ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTif gs)) f monoF P₁ P₂ P₁⊆P₂ i wp =
        monoIf gs f monoF wp
        where
        monoIf
          : (gs : Guards Unit)
            (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → PredTrans _)
            (monoF : ∀ r → MonoPredTrans (f r))
            (wp : PTGuards P₁ i gs f)
            → PTGuards P₂ i gs f
        monoIf (otherwise≔ x) f monoF wp =
          monoF (Level.lift zero) _ _ P₁⊆P₂ i wp
        monoIf (clause (b ≔ c) gs) f monoF wp
          with toBool b
        ... | true =
            (λ _ → monoF (Level.lift zero) _ _ P₁⊆P₂ i (proj₁ wp refl))
          , (λ ())
        ... | false =
            (λ ())
          , (λ _ →
             monoIf gs
               (λ where (Level.lift i) → f (Level.lift (suc i)))
               (λ where (Level.lift i) → monoF (Level.lift (suc i)) ) (proj₂ wp refl))
      proj₁ (ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTeither A₁ A₂ .(Left l))) f monoF P₁ P₂ P₁⊆P₂ i (wpₗ , wpᵣ)) l refl =
        monoF (Level.lift (Left l)) _ _ P₁⊆P₂ i (wpₗ l refl)
      proj₂ (ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTeither A₁ A₂ .(Right r))) f monoF P₁ P₂ P₁⊆P₂ i (wpₗ , wpᵣ)) r refl =
        monoF (Level.lift (Right r)) _ _ P₁⊆P₂ i (wpᵣ r refl)
      proj₁ (ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTmaybe A₁ .nothing)) f monoF P₁ P₂ P₁⊆P₂ i (wpₙ , wpⱼ)) refl =
        monoF (Level.lift nothing) _ _ P₁⊆P₂ i (wpₙ refl)
      proj₂ (ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTmaybe A₁ .(just j))) f monoF P₁ P₂ P₁⊆P₂ i (wpₙ , wpⱼ)) j refl =
        monoF (Level.lift (just j)) _ _ P₁⊆P₂ i (wpⱼ j refl)
      ASTPredTransMono.opPTMono₂ monoPTBranch (Left  c) f₁ f₂ f₁⊑f₂ P i x =
        opPTMono₂ c f₁ f₂ f₁⊑f₂ P i x
      ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTif gs)) f₁ f₂ f₁⊑f₂ P i wp =
        monoIf gs _ _ f₁⊑f₂ wp
        where
        monoIf
          : (gs : Guards Unit)
            (f₁ f₂ : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → PredTrans _)
            (f₁⊑f₂ : ∀ r → f₁ r ⊑ f₂ r)
            (wp : PTGuards P i gs f₁)
            → PTGuards P i gs f₂
        monoIf (otherwise≔ x) f₁ f₂ f₁⊑f₂ wp =
          f₁⊑f₂ (Level.lift zero) P i wp
        monoIf (clause (b ≔ c) gs) f₁ f₂ f₁⊑f₂ wp
          with toBool b
        ... | true =
            (λ _ → f₁⊑f₂ (Level.lift zero) P i (proj₁ wp refl))
          , (λ ())
        ... | false =
            (λ ())
          , λ _ →
              monoIf gs
                (λ where (Level.lift i) → f₁ (Level.lift (suc i)))
                (λ where (Level.lift i) → f₂ (Level.lift (suc i)))
                (λ where (Level.lift i) → f₁⊑f₂ (Level.lift (suc i)))
                (proj₂ wp refl)
      proj₁ (ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTeither A₁ A₂ .(Left l))) f₁ f₂ f₁⊑f₂ P i (wpₗ , wpᵣ)) l refl =
        f₁⊑f₂ (Level.lift (Left l)) P i (wpₗ _ refl)
      proj₂ (ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTeither A₁ A₂ .(Right r))) f₁ f₂ f₁⊑f₂ P i (wpₗ , wpᵣ)) r refl =
        f₁⊑f₂ (Level.lift (Right r)) P i (wpᵣ _ refl)
      proj₁ (ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTmaybe A₁ .nothing)) f₁ f₂ f₁⊑f₂ P i (wpₙ , wpⱼ)) refl =
        f₁⊑f₂ (Level.lift nothing) P i (wpₙ refl)
      proj₂ (ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTmaybe A₁ .(just j))) f₁ f₂ f₁⊑f₂ P i (wpₙ , wpⱼ)) j refl =
        f₁⊑f₂ (Level.lift (just j)) P i (wpⱼ _ refl)

      unextendPT : ∀ {A} (m : AST CBranch RBranch A)
                   → predTrans PTBranch m ⊑ predTrans PT (unextendBranch m)
      unextendPT (ASTreturn x) P i wp = wp
      unextendPT (ASTbind m f) P i wp =
        predTransMono (unextendBranch m)
          (bindPT PTBranch (predTrans PTBranch ∘ f) i P)
          (bindPT PT (predTrans PT ∘ unextendBranch ∘ f) i P)
          (bindPTMono₂ (predTrans PTBranch ∘ f) (predTrans PT ∘ unextendBranch ∘ f) (unextendPT ∘ f) i P)
          i (unextendPT m _ _ wp)
      unextendPT (ASTop (Left c) f) P i wp =
        opPTMono₂ c (predTrans PTBranch ∘ f) (predTrans PT ∘ unextendBranch ∘ f) (unextendPT ∘ f) P i wp
      unextendPT (ASTop{A} (Right (Branching.ASTif gs)) f) P i wp =
        unextendPTGuards gs f (unextendPT ∘ f) wp
        where
        unextendPTGuards
          : (gs : Guards Unit)
            → (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → AST CBranch RBranch A)
            → ((i : Level.Lift (Level.# 1) (Fin (lengthGuards gs)))
               → predTrans PTBranch (f i) ⊑ predTrans PT (unextendBranch (f i)))
            → PTGuards P i gs (predTrans PTBranch ∘ f)
            → predTrans PT (unextendGuards gs (unextendBranch ∘ f)) P i
        unextendPTGuards (otherwise≔ x) f ih wp =
          ih (Level.lift Fin.zero) P i wp
        unextendPTGuards (clause (b ≔ c) gs) f ih wp
          with toBool b
        ... | true = ih (Level.lift Fin.zero) P i (proj₁ wp refl)
        ... | false =
          unextendPTGuards gs
            (λ where (Level.lift i) → f (Level.lift (suc i)))
            (λ where (Level.lift i) → ih (Level.lift (suc i)))
            (proj₂ wp refl)
      unextendPT (ASTop (Right (Branching.ASTeither A₁ A₂ (Left x))) f) P i wp =
        unextendPT (f (Level.lift (Left x))) P i (proj₁ wp x refl)
      unextendPT (ASTop (Right (Branching.ASTeither A₁ A₂ (Right y))) f) P i wp =
        unextendPT (f (Level.lift (Right y))) P i (proj₂ wp y refl)
      unextendPT (ASTop (Right (Branching.ASTmaybe A₁ (just x))) f) P i wp =
        unextendPT (f (Level.lift (just x))) P i (proj₂ wp x refl)
      unextendPT (ASTop (Right (Branching.ASTmaybe A₁ nothing)) f) P i wp =
        unextendPT (f (Level.lift nothing)) P i (proj₁ wp refl)

      extendPT :  ∀ {A} (m : AST CBranch RBranch A)
                 → predTrans PT (unextendBranch m) ⊑ predTrans PTBranch m
      extendPT (ASTreturn x) P i wp = wp
      extendPT (ASTbind m f) P i wp =
        ASTPredTransMono.predTransMono monoPTBranch m
          (bindPT PT (predTrans PT ∘ unextendBranch ∘ f) i P)
          _
          (bindPTMono₂ _ _ (extendPT ∘ f) i P)
          i (extendPT m _ i wp)
      extendPT (ASTop (Left x) f) P i wp =
        opPTMono₂ x (predTrans PT ∘ unextendBranch ∘ f) (predTrans PTBranch ∘ f)
          (extendPT ∘ f) P i wp
      extendPT (ASTop{A} (Right (Branching.ASTif gs)) f) P i wp =
        extendGuards gs f (extendPT ∘ f) wp
        where
        extendGuards
          : (gs : Guards Unit)
            → (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → AST CBranch RBranch A)
            → ((i : Level.Lift (Level.# 1) (Fin (lengthGuards gs)))
               → predTrans PT (unextendBranch (f i)) ⊑ predTrans PTBranch (f i))
            → predTrans PT (unextendGuards gs (unextendBranch ∘ f)) P i
            → PTGuards P i gs (predTrans PTBranch ∘ f)
        extendGuards (otherwise≔ x) f ih wp =
          ih (Level.lift zero) P i wp
        extendGuards (clause (b ≔ c) gs) f ih wp
          with toBool b
        ... | false =
            (λ ())
          , (λ _ → extendGuards gs (λ where (Level.lift i) → f (Level.lift (suc i)))
                     (λ where (Level.lift i) → ih (Level.lift (suc i)))
                     wp)
        ... | true =
            (λ _ → ih (Level.lift zero) P i wp)
          , (λ ())

      extendPT (ASTop (Right (Branching.ASTeither A₁ A₂ (Left x))) f) P i wp =
          (λ where .x refl → extendPT (f (Level.lift (Left x))) P i wp)
        , λ where _ ()
      extendPT (ASTop (Right (Branching.ASTeither A₁ A₂ (Right y))) f) P i wp =
          (λ where _ ())
        , (λ where .y refl → extendPT (f (Level.lift (Right y))) P i wp)
      extendPT (ASTop (Right (Branching.ASTmaybe A₁ x)) f) P i wp =
          (λ where refl → extendPT (f (Level.lift nothing)) P i wp)
        , (λ where j refl → extendPT (f (Level.lift (just j))) P i wp)

  module Sufficient (Types : ASTTypes)
    (OS : ASTOpSem C R Types)
    (PT : ASTPredTrans C R Types)
    (PTMono : ASTPredTransMono C R Types PT)
    (SU : ASTSufficientPT C R Types OS PT) where

    open OpSem Types OS
    open PT Types PT

    BranchSuf : ASTSufficientPT CBranch RBranch Types OSBranch PTBranch
    ASTSufficientPT.returnSuf BranchSuf x P i wp =
      ASTSufficientPT.returnSuf SU x P i wp
    ASTSufficientPT.bindSuf BranchSuf{A}{B} m f mSuf fSuf P i wp =
      ASTSufficientPT.bindSuf SU (unextendBranch m) (unextendBranch ∘ f)
        mSuf' fSuf'
        P i
        (unextendPT PTMono (ASTbind m f) P i wp)
      where
      mSuf' : ASTSufficientPT.Sufficient SU A (unextendBranch m)
      mSuf' P i wp =
        mSuf P i (extendPT PTMono m P i wp)

      fSuf' : ∀ x → ASTSufficientPT.Sufficient SU _ (unextendBranch (f x))
      fSuf' x P i wp =
        fSuf x P i (extendPT PTMono (f x) P i wp)
        
    ASTSufficientPT.opSuf BranchSuf (Left c) f fSuf P i wp =
      ASTSufficientPT.opSuf SU c (unextendBranch ∘ f) fSuf' P i
        (unextendPT PTMono (ASTop (Left c) f) P i wp)
      where
      fSuf' : ∀ r → ASTSufficientPT.Sufficient SU _ (unextendBranch (f r))
      fSuf' r P i wp =
        fSuf r P i (extendPT PTMono (f r) P i wp)
    ASTSufficientPT.opSuf BranchSuf (Right (Branching.ASTif gs)) f fSuf P i wp =
      GuardsSuf gs f fSuf wp
      where
      GuardsSuf
        : (gs : Guards Unit) (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → AST CBranch RBranch _)
          → (∀ i → ASTSufficientPT.Sufficient BranchSuf _ (f i))
          → PTGuards P i gs (ASTPredTrans.predTrans PTBranch ∘ f)
          → P (ASTOpSem.runM OS (ASTOpSem.runAST OS (unextendGuards gs (unextendBranch ∘ f))) i)
      GuardsSuf (otherwise≔ x₁) f fSuf wp =
        fSuf (Level.lift zero) P i wp
      GuardsSuf (clause (b ≔ c) gs) f fSuf wp
        with toBool b
      ... | true = fSuf (Level.lift zero) P i (proj₁ wp refl)
      ... | false =
        GuardsSuf gs
          (λ where (Level.lift i) → f (Level.lift (suc i)))
          (λ where (Level.lift i) → fSuf (Level.lift (suc i)))
          (proj₂ wp refl)
    ASTSufficientPT.opSuf BranchSuf (Right (Branching.ASTeither A₁ A₂ (Left x))) f fSuf P i wp =
      fSuf (Level.lift (Left x)) P i (proj₁ wp x refl)
    ASTSufficientPT.opSuf BranchSuf (Right (Branching.ASTeither A₁ A₂ (Right y))) f fSuf P i wp =
      fSuf (Level.lift (Right y)) P i (proj₂ wp y refl)
    ASTSufficientPT.opSuf BranchSuf (Right (Branching.ASTmaybe A₁ (just x))) f fSuf P i wp =
      fSuf (Level.lift (just x)) P i (proj₂ wp x refl)
    ASTSufficientPT.opSuf BranchSuf (Right (Branching.ASTmaybe A₁ nothing)) f fSuf P i wp =
      fSuf (Level.lift nothing) P i (proj₁ wp refl)

