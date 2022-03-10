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

-- -- Coherence
--   runMIdLeft  : ∀ {A} (x : A) (f : A → AST C R A) (i : Input)
--                 →   runM (runAST (ASTbind (ASTreturn x) f)) i
--                   ≡ runM (runAST (f x)) i
--   runMIdRight : ∀ {A} (m : AST C R A) (i : Input)
--                 →   runM (runAST (ASTbind m ASTreturn)) i
--                   ≡ runM (runAST m) i
--   runMAssoc   : ∀ {A B₁ B₂} (m : AST C R A) (f : A → AST C R B₁) (g : B₁ → AST C R B₂) (i : Input)
--                 →   runM (runAST (ASTbind (ASTbind m f) g)) i
--                   ≡ runM (runAST (ASTbind m (λ x → ASTbind (f x) g))) i

-- record ASTOpSemLaws
--   (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
--   (Types : ASTTypes)
--   (OS : ASTOpSem C R Types)
--   (mb : MonadASTBind (ASTOpSem.M OS))
--   : Set₁ where
--   open ASTOpSem OS
--   field
--   -- Coherence
--     runMIdLeft  : ∀ {A} (x : A) (c : Cₘ) (f : A → AST Cₘ Rₘ C R A) (i : Input)
--                   →   runM (runAST (ASTbind c (ASTreturn (MonadASTBind.return mb x)) f)) i
--                     ≡ runM (runAST (f x)) i
--     -- runMIdRight : ∀ {A} (c : Cₘ) (m : AST Cₘ Rₘ C R (Rₘ c A)) (i : Input)
--     --               →   runM (runAST (ASTbind c m ASTreturn)) i
--     --                 ≡ runM (let x = runAST m in {!!}) i -- runM (runAST m) i
--     runMAssoc   : ∀ {A B₁ B₂} (c₁ c₂ : Cₘ) (m : AST Cₘ Rₘ C R (Rₘ c₂ A)) (f : A → AST Cₘ Rₘ C R (Rₘ c₁ B₁)) (g : B₁ → AST Cₘ Rₘ C R (Rₘ c₂ B₂)) (i : Input)
--                   →   runM (runAST (ASTbind c₁ (ASTbind c₂ m f) g)) i
--                     ≡ runM (runAST (ASTbind c₂ m (λ x → ASTbind c₁ (f x) g))) i

module TrivASTBind where
  Cₘ : Set
  Cₘ = Unit

  Rₘ : Cₘ → Set → Set
  Rₘ _ = id

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



--   MonoBindPTS : Set₁
--   MonoBindPTS = ∀ {A B} (f₁ f₂ : A → PredTrans B) → (∀ x → f₁ x ⊑ f₂ x)
--                 → ∀ c i P o → bindPTS c f₁ i P o → bindPTS c f₂ i P o

--   ptAST : ∀ {A} → AST Cₘ Rₘ C R A → PredTrans A
--   ptAST (ASTreturn x) = returnPTS x
--   ptAST (ASTbind c p f) Post input =
--     ptAST p (bindPTS c (λ x → ptAST ((f x))) input Post) input
--   ptAST (ASTop c f) Post = opPTS c (λ r → ptAST (f r)) Post

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
--   field
--     returnSuf : ∀ {A} (x : A) {P} {i} → Sufficient A (ASTreturn x) P i
--     bindSuf   : ∀ {A B} (c : Cₘ) (m : AST Cₘ Rₘ C R (Rₘ c A)) (f : A → AST Cₘ Rₘ C R B)
--                 → (ih : ∀ x P i → Sufficient B (f x) P i)
--                 → ∀ P i
--                 → (bp : bindPTS c (λ x' → ptAST (f x')) i P (runM (runAST m) i))
--                 → P (runM (runAST (ASTbind c m f)) i)
--     opSuf     : ∀ {A} (c : C A) (f : R A c → AST Cₘ Rₘ C R A)
--                 → (ih : ∀ P i r → Sufficient A (f r) P i)
--                 → ∀ P i
--                 → (op : opPTS c (λ r → ptAST (f r)) P i)
--                 → P (runM (runAST (ASTop c f)) i)

--   sufficient : ∀ {A} → (m : AST Cₘ Rₘ C R A) (P : Post A) (i : Input) → Sufficient A m P i
--   sufficient (ASTreturn x) P i wp = returnSuf x wp
--   sufficient (ASTbind c m f) P i wp
--     with sufficient m _ i wp
--   ... | wp' = bindSuf c m f (sufficient ∘ f) P i wp'
--   sufficient{A} (ASTop c f) P i wp =
--     opSuf c f ih P i wp
--     where
--     ih : (P : Post A) (i : Input) (r : R A c) → Sufficient A (f r) P i
--     ih P i r = sufficient (f r) P i

-- module RWS (Ev Wr St : Set) where

--   data C (A : Set) : Set₁ where
--     RWSgets  : (g : St → A) → C A
--     RWSputs  : (p : St → St) → A ≡ Unit → C A
--     RWSask   : (A ≡ Ev) → C A
--     RWSlocal : (l : Ev → Ev) → C A
--     RWStell  : (outs : List Wr) → (A ≡ Unit) → C A

--   R : (A : Set) (c : C A) → Set₁
--   R A (RWSgets x) = Level.Lift _ ⊥
--   R .Unit (RWSputs f refl) = Level.Lift _ ⊥
--   R .Ev (RWSask refl) = Level.Lift _ ⊥
--   R A (RWSlocal x) = Level.Lift _ ⊤
--   R A (RWStell x refl) = Level.Lift _ ⊥

--   RWS : Set → Set₁
--   RWS = AST TrivASTBind.Cₘ TrivASTBind.Rₘ C R

--   Types : ASTTypes
--   ASTTypes.Input Types = Ev × St
--   ASTTypes.Output Types A = A × St × List Wr

--   M : Set → Set
--   M A = ASTTypes.Input Types → ASTTypes.Output Types A

--   monadAST : MonadASTImpl TrivASTBind.Cₘ TrivASTBind.Rₘ C R M
--   MonadASTImpl.ret monadAST x (ev , st) = x , st , []
--   MonadASTImpl.bind monadAST _ m f i@(ev , st₀) =
--     let (x₁ , st₁ , outs₁) = m i
--         (x₂ , st₂ , outs₂) = f x₁ (ev , st₁)
--     in  (x₂ , st₂ , outs₁ ++ outs₂)
--   MonadASTImpl.op monadAST (RWSgets g) _ i@(ev , st) =
--     g st , st , []
--   MonadASTImpl.op monadAST (RWSputs p refl) _ i@(ev , st) =
--     unit , p st , []
--   MonadASTImpl.op monadAST (RWSask refl) _ i@(ev , st) =
--     ev , st , []
--   MonadASTImpl.op monadAST (RWSlocal l) f i@(ev , st) =
--     f (Level.lift tt) (l ev , st)
--   MonadASTImpl.op monadAST (RWStell outs refl) _ i@(ev , st) =
--     unit , st , outs

--   OS = SimpleASTOpSem.OS TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types monadAST

--   RWSPredTrans = ASTPredTrans TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types

--   RWSbindPost : List Wr → {A : Set} → (A × St × List Wr → Set) → (A × St × List Wr → Set)
--   RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

--   PT : RWSPredTrans
--   ASTPredTrans.returnPTS PT x P (ev , st) =
--     P (x , st , [])
--   ASTPredTrans.bindPTS PT c f (ev , stₒ) P (x , st₁ , outs₁) =
--     ∀ r → r ≡ x → f r (RWSbindPost outs₁ P) (ev , st₁)
--   ASTPredTrans.opPTS PT (RWSgets g) f P (ev , pre) =
--     P (g pre , pre , [])
--   ASTPredTrans.opPTS PT (RWSputs p refl) f P (ev , pre) =
--     P (unit , p pre , [])
--   ASTPredTrans.opPTS PT (RWSask refl) f P (ev , pre) =
--     P (ev , pre , [])
--   ASTPredTrans.opPTS PT (RWSlocal l) f P (ev , pre) =
--     ∀ ev' → ev' ≡ l ev → f (Level.lift tt) P (ev' , pre)
--   ASTPredTrans.opPTS PT (RWStell outs refl) f P (ev , pre) =
--     P (unit , pre , outs)

--   RWSSufficientPre =
--     ASTSufficientPre TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types OS PT

--   SufPre : RWSSufficientPre
--   ASTSufficientPre.returnSuf SufPre x wp = wp
--   ASTSufficientPre.bindSuf SufPre c m f suf P i@(ev , st₀) wp =
--     let (x₁ , st₁ , outs₁) = ASTOpSem.runAST OS m i
--     in suf x₁ (RWSbindPost outs₁ P) ((ev , st₁)) (wp x₁ refl)
--   ASTSufficientPre.opSuf SufPre (RWSgets g) f ih P i@(ev , st₀) op₁ =
--     op₁
--   ASTSufficientPre.opSuf SufPre (RWSputs p refl) f ih P i@(ev , st₀) op₁ =
--     op₁
--   ASTSufficientPre.opSuf SufPre (RWSask refl) f ih P i@(ev , st₀) op₁ = op₁
--   ASTSufficientPre.opSuf SufPre (RWSlocal l) f ih P i@(ev , st₀) op₁ =
--     ih P (l ev , st₀) (Level.lift tt) (op₁ (l ev) refl)
--   ASTSufficientPre.opSuf SufPre (RWStell outs refl) f ih P i@(ev , st₀) op₁ =
--     op₁

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
      ASTPredTransMono.opPTMono₁ monoPTBranch (Right (Branching.ASTif x)) f monoF P₁ P₂ P₁⊆P₂ i wp = {!!}
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
      ASTPredTransMono.opPTMono₂ monoPTBranch (Right (Branching.ASTif x₁)) f₁ f₂ f₁⊑f₂ P i x = {!!}
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

--     SufBranch : ASTSufficientPre Cₘ Rₘ CBranch RBranch Types OSBranch PTBranch
--     ASTSufficientPre.returnSuf SufBranch x wp =
--       ASTSufficientPre.returnSuf SU x wp
--     ASTSufficientPre.bindSuf SufBranch{A}{B} c m f ih P i bp =
--       ASTSufficientPre.bindSuf SU c (unextendBranch m) (unextendBranch ∘ f)
--         {!!} P i {!!}
--       where
--       pt₁ pt₂ : ∀ {B} → AST Cₘ Rₘ CBranch RBranch B
--                 → ASTPredTrans.PredTrans PT B
--       pt₁ x' = ASTPredTrans.ptAST PTBranch x'

--       pt₂ x' = ASTPredTrans.ptAST PT (unextendBranch x')

--       lem : ∀ {B} x' → ASTPredTrans._⊑_ PT (pt₁{B} x') (pt₂ x')
--       lem (ASTreturn x) P i pf = pf
--       lem (ASTbind c x' f) P i pf =
--         lem x' {!!} i {!!}
--       lem (ASTop c f) P i pf = {!!}

--     ASTSufficientPre.opSuf SufBranch = {!!}

-- -- --   module Sufficient (Types : ASTTypes)
-- -- --     (interpOS : ASTOpSem C R Types) (interpPT : ASTPredTrans C R Types)
-- -- --     (suf : ASTWeakestPre C R Types interpOS interpPT)
-- -- --     where

-- -- --     -- open ASTOpSem      interpOS
-- -- --     -- open OpSem         interpOS
-- -- --     -- open ASTPredTrans  interpPT
-- -- --     -- open PT            interpPT
-- -- --     -- open ASTWeakestPre suf

-- -- --     -- BranchExtendWeakestPre :
-- -- --     --   ASTWeakestPre CBranch RBranch BranchExtendOpSem BranchExtendPredTrans
-- -- --     -- ASTWeakestPre.runM     BranchExtendWeakestPre = runM
-- -- --     -- ASTWeakestPre.returnPT BranchExtendWeakestPre = returnPT

-- -- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTreturn x) f wp ih = {!!}
-- -- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTbind m x) f wp ih = {!!}
-- -- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTop c x) f wp ih = {!!}

-- -- --     -- ASTWeakestPre.opPT     BranchExtendWeakestPre = {!!}
