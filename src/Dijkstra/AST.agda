{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST where

open import Data.Empty
open import Data.Fin
open import Data.Product using (_×_ ; _,_)
open import Data.Unit
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)
open import Relation.Binary.PropositionalEquality

data AST
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁) : Set → Set₁ where
  -- monadic operations
  ASTreturn : ∀ {A} → A → AST Cₘ Rₘ Cₒ Rₒ A
  ASTbind   : ∀ {A B} → (c : Cₘ) (m : AST Cₘ Rₘ Cₒ Rₒ (Rₘ c A)) (f : A → AST Cₘ Rₘ Cₒ Rₒ B)
              → AST Cₘ Rₘ Cₒ Rₒ B
  -- effect operations
  ASTop : ∀ {A} → (c : Cₒ A) (f : Rₒ A c → AST Cₘ Rₘ Cₒ Rₒ A) → AST Cₘ Rₘ Cₒ Rₒ A

record ASTOpSemTypes : Set₁ where
  constructor mkASTOpSemTypes
  field
    Input  : Set
    Output : (A : Set) → Set

record ASTImpl
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁) : Set₁ where
  constructor mkASTImpl
  field
    M : Set → Set
    runAST : ∀ {A} → AST Cₘ Rₘ Cₒ Rₒ A → M A

record MonadASTImpl
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (M : Set → Set): Set₁ where
  field
    ret : ∀ {A} → A → M A
    bind   : ∀ {A B} → (c : Cₘ) (m : M (Rₘ c A)) (f : A → M B) → M B
    op     : ∀ {A}  → (c : Cₒ A) (f : Rₒ A c → M A) → M A

  impl : ASTImpl Cₘ Rₘ Cₒ Rₒ
  ASTImpl.M impl = M
  ASTImpl.runAST impl (ASTreturn x) = ret x
  ASTImpl.runAST impl (ASTbind c x f) = bind c (ASTImpl.runAST impl x) (ASTImpl.runAST impl ∘ f)
  ASTImpl.runAST impl (ASTop c f) = op c (ASTImpl.runAST impl ∘ f)
open MonadASTImpl ⦃ ... ⦄ public
  hiding (impl)

record ASTOpSem
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes) : Set₁ where
  constructor mkASTOpSem
  open ASTOpSemTypes Types public
  field
    impl : ASTImpl Cₘ Rₘ Cₒ Rₒ
  open ASTImpl impl public
  field
    runM : ∀ {A} → M A → Input → Output A

--   -- -- Coherence
--   --   runMIdLeft  : ∀ {A} (x : A) (f : A → AST C R A) (i : Input)
--   --                 →   runM (runAST (ASTbind (ASTreturn x) f)) i
--   --                   ≡ runM (runAST (f x)) i
--   --   runMIdRight : ∀ {A} (m : AST C R A) (i : Input)
--   --                 →   runM (runAST (ASTbind m ASTreturn)) i
--   --                   ≡ runM (runAST m) i
--   --   runMAssoc   : ∀ {A B₁ B₂} (m : AST C R A) (f : A → AST C R B₁) (g : B₁ → AST C R B₂) (i : Input)
--   --                 →   runM (runAST (ASTbind (ASTbind m f) g)) i
--   --                   ≡ runM (runAST (ASTbind m (λ x → ASTbind (f x) g))) i

record MonadASTBind
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set) (M : Set → Set) : Set₁ where
  field
    return : ∀ {A c} → A → Rₘ c A
    bind   : ∀ {A B c} → M (Rₘ c A) → (A → M B) → M B

record ASTOpSemLaws
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes)
  (OS : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types)
  (mb : MonadASTBind Cₘ Rₘ (ASTOpSem.M OS))
  : Set₁ where
  open ASTOpSem OS
  field
  -- Coherence
    runMIdLeft  : ∀ {A} (x : A) (c : Cₘ) (f : A → AST Cₘ Rₘ Cₒ Rₒ A) (i : Input)
                  →   runM (runAST (ASTbind c (ASTreturn (MonadASTBind.return mb x)) f)) i
                    ≡ runM (runAST (f x)) i
    -- runMIdRight : ∀ {A} (c : Cₘ) (m : AST Cₘ Rₘ Cₒ Rₒ (Rₘ c A)) (i : Input)
    --               →   runM (runAST (ASTbind c m ASTreturn)) i
    --                 ≡ runM (let x = runAST m in {!!}) i -- runM (runAST m) i
    runMAssoc   : ∀ {A B₁ B₂} (c₁ c₂ : Cₘ) (m : AST Cₘ Rₘ Cₒ Rₒ (Rₘ c₂ A)) (f : A → AST Cₘ Rₘ Cₒ Rₒ (Rₘ c₁ B₁)) (g : B₁ → AST Cₘ Rₘ Cₒ Rₒ (Rₘ c₂ B₂)) (i : Input)
                  →   runM (runAST (ASTbind c₁ (ASTbind c₂ m f) g)) i
                    ≡ runM (runAST (ASTbind c₂ m (λ x → ASTbind c₁ (f x) g))) i

module TrivASTBind where
  Cₘ : Set
  Cₘ = Unit

  Rₘ : Cₘ → Set → Set
  Rₘ _ = id

module SimpleASTOpSem
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes)
  (monadOp : MonadASTImpl Cₘ Rₘ Cₒ Rₒ λ A → ASTOpSemTypes.Input Types → ASTOpSemTypes.Output Types A) where

  OS : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types
  ASTOpSem.impl OS = MonadASTImpl.impl monadOp
  ASTOpSem.runM OS = id

record ASTPredTrans
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes) : Set₂ where
  constructor mkASTPredTrans
  open ASTOpSemTypes Types public

  Pre : Set₁
  Pre = (i : Input) → Set

  Post : Set → Set₁
  Post A = Output A → Set

  PredTrans : (A : Set) → Set₁
  PredTrans A = (P : Post A) → Pre

  _⊆_ : (P₁ P₂ : Pre) → Set
  P₁ ⊆ P₂ = ∀ i → P₁ i → P₂ i

  _⊑_ : {A : Set} → (pt₁ pt₂ : PredTrans A) → Set₁
  pt₁ ⊑ pt₂ = ∀ P → pt₁ P ⊆ pt₂ P
  
  field
    returnPTS : ∀ {A} → A → PredTrans A
    bindPTS   : ∀ {A B} → (c : Cₘ) (f : A → PredTrans B) (i : Input) (P : Post B) → Post (Rₘ c A)
    opPTS     : ∀ {A} → (c : Cₒ A) → (Rₒ A c → PredTrans A) → PredTrans A

  MonoBindPTS : Set₁
  MonoBindPTS = ∀ {A B} (f₁ f₂ : A → PredTrans B) → (∀ x → f₁ x ⊑ f₂ x)
                → ∀ c i P o → bindPTS c f₁ i P o → bindPTS c f₂ i P o

  ptAST : ∀ {A} → AST Cₘ Rₘ Cₒ Rₒ A → PredTrans A
  ptAST (ASTreturn x) = returnPTS x
  ptAST (ASTbind c p f) Post input =
    ptAST p (bindPTS c (λ x → ptAST ((f x))) input Post) input
  ptAST (ASTop c f) Post = opPTS c (λ r → ptAST (f r)) Post

record ASTSufficientPre
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes)
  (os : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types) (pt : ASTPredTrans Cₘ Rₘ Cₒ Rₒ Types) : Set₁ where
  constructor mkASTSufficientPre
  open ASTOpSem     os
  open ASTPredTrans pt
    hiding (Input ; Output)

  Sufficient : (A : Set) (m : AST Cₘ Rₘ Cₒ Rₒ A) (P : Post A) (i : Input) → Set
  Sufficient A m P i =
    (wp : ptAST m P i) → P (runM (runAST m) i)

  field
    returnSuf : ∀ {A} (x : A) {P} {i} → Sufficient A (ASTreturn x) P i
    bindSuf   : ∀ {A B} (c : Cₘ) (m : AST Cₘ Rₘ Cₒ Rₒ (Rₘ c A)) (f : A → AST Cₘ Rₘ Cₒ Rₒ B)
                → (ih : ∀ x P i → Sufficient B (f x) P i)
                → ∀ P i
                → (bp : bindPTS c (λ x' → ptAST (f x')) i P (runM (runAST m) i))
                → P (runM (runAST (ASTbind c m f)) i)
    opSuf     : ∀ {A} (c : Cₒ A) (f : Rₒ A c → AST Cₘ Rₘ Cₒ Rₒ A)
                → (ih : ∀ P i r → Sufficient A (f r) P i)
                → ∀ P i
                → (op : opPTS c (λ r → ptAST (f r)) P i)
                → P (runM (runAST (ASTop c f)) i)

  sufficient : ∀ {A} → (m : AST Cₘ Rₘ Cₒ Rₒ A) (P : Post A) (i : Input) → Sufficient A m P i
  sufficient (ASTreturn x) P i wp = returnSuf x wp
  sufficient (ASTbind c m f) P i wp
    with sufficient m _ i wp
  ... | wp' = bindSuf c m f (sufficient ∘ f) P i wp'
  sufficient{A} (ASTop c f) P i wp =
    opSuf c f ih P i wp
    where
    ih : (P : Post A) (i : Input) (r : Rₒ A c) → Sufficient A (f r) P i
    ih P i r = sufficient (f r) P i

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
  RWS = AST TrivASTBind.Cₘ TrivASTBind.Rₘ C R

  Types : ASTOpSemTypes
  ASTOpSemTypes.Input Types = Ev × St
  ASTOpSemTypes.Output Types A = A × St × List Wr

  M : Set → Set
  M A = ASTOpSemTypes.Input Types → ASTOpSemTypes.Output Types A

  monadAST : MonadASTImpl TrivASTBind.Cₘ TrivASTBind.Rₘ C R M
  MonadASTImpl.ret monadAST x (ev , st) = x , st , []
  MonadASTImpl.bind monadAST _ m f i@(ev , st₀) =
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

  OS = SimpleASTOpSem.OS TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types monadAST

  RWSPredTrans = ASTPredTrans TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types

  RWSbindPost : List Wr → {A : Set} → (A × St × List Wr → Set) → (A × St × List Wr → Set)
  RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

  PT : RWSPredTrans
  ASTPredTrans.returnPTS PT x P (ev , st) =
    P (x , st , [])
  ASTPredTrans.bindPTS PT c f (ev , stₒ) P (x , st₁ , outs₁) =
    ∀ r → r ≡ x → f r (RWSbindPost outs₁ P) (ev , st₁)
  ASTPredTrans.opPTS PT (RWSgets g) f P (ev , pre) =
    P (g pre , pre , [])
  ASTPredTrans.opPTS PT (RWSputs p refl) f P (ev , pre) =
    P (unit , p pre , [])
  ASTPredTrans.opPTS PT (RWSask refl) f P (ev , pre) =
    P (ev , pre , [])
  ASTPredTrans.opPTS PT (RWSlocal l) f P (ev , pre) =
    ∀ ev' → ev' ≡ l ev → f (Level.lift tt) P (ev' , pre)
  ASTPredTrans.opPTS PT (RWStell outs refl) f P (ev , pre) =
    P (unit , pre , outs)

  RWSSufficientPre =
    ASTSufficientPre TrivASTBind.Cₘ TrivASTBind.Rₘ C R Types OS PT

  SufPre : RWSSufficientPre
  ASTSufficientPre.returnSuf SufPre x wp = wp
  ASTSufficientPre.bindSuf SufPre c m f suf P i@(ev , st₀) wp =
    let (x₁ , st₁ , outs₁) = ASTOpSem.runAST OS m i
    in suf x₁ (RWSbindPost outs₁ P) ((ev , st₁)) (wp x₁ refl)
  ASTSufficientPre.opSuf SufPre (RWSgets g) f ih P i@(ev , st₀) op₁ =
    op₁
  ASTSufficientPre.opSuf SufPre (RWSputs p refl) f ih P i@(ev , st₀) op₁ =
    op₁
  ASTSufficientPre.opSuf SufPre (RWSask refl) f ih P i@(ev , st₀) op₁ = op₁
  ASTSufficientPre.opSuf SufPre (RWSlocal l) f ih P i@(ev , st₀) op₁ =
    ih P (l ev , st₀) (Level.lift tt) (op₁ (l ev) refl)
  ASTSufficientPre.opSuf SufPre (RWStell outs refl) f ih P i@(ev , st₀) op₁ =
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
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  where

  CBranch : Set → Set₁
  CBranch A = Either (Cₒ A) (Branching.C A)

  RBranch : (A : Set) (c : CBranch A) → Set₁
  RBranch A (Left x) = Rₒ A x
  RBranch A (Right y) = Branching.R A y

  unextendGuards
    : ∀ {A} → (gs : Guards{b = Level.zero} Unit) (f : Level.Lift (Level.# 1) (Fin (lengthGuards gs)) → AST Cₘ Rₘ Cₒ Rₒ A)
      → AST Cₘ Rₘ Cₒ Rₒ A
  unextendGuards (otherwise≔ _) f = f (Level.lift zero)
  unextendGuards (clause (b ≔ c) gs) f =
    if (toBool b) then (f (Level.lift zero)) else
      (unextendGuards gs (λ where (Level.lift i) → f (Level.lift (suc i))))

  unextendBranch : ∀ {A} → AST Cₘ Rₘ CBranch RBranch A → AST Cₘ Rₘ Cₒ Rₒ A
  unextendBranch (ASTreturn x) = ASTreturn x
  unextendBranch (ASTbind c x f) = ASTbind c (unextendBranch x) (unextendBranch ∘ f)
  unextendBranch (ASTop (Left x) f) = ASTop x (unextendBranch ∘ f)
  unextendBranch (ASTop (Right (Branching.ASTif gs)) f) =
    unextendGuards gs (unextendBranch ∘ f)
  unextendBranch (ASTop (Right (Branching.ASTeither A₁ A₂ x)) f) =
    unextendBranch (f (Level.lift x))
  unextendBranch (ASTop (Right (Branching.ASTmaybe A₁ x)) f) =
    unextendBranch (f (Level.lift x))

  module OpSem (Types : ASTOpSemTypes) (OS : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types) where

    OSBranch : ASTOpSem Cₘ Rₘ CBranch RBranch Types
    ASTImpl.M (ASTOpSem.impl OSBranch) =
      ASTImpl.M (ASTOpSem.impl OS)
    ASTImpl.runAST (ASTOpSem.impl OSBranch) x =
      ASTImpl.runAST (ASTOpSem.impl OS) (unextendBranch x)
    ASTOpSem.runM OSBranch = ASTOpSem.runM OS

  module PT (Types : ASTOpSemTypes) (PT : ASTPredTrans Cₘ Rₘ Cₒ Rₒ Types) where

    PTBranch : ASTPredTrans Cₘ Rₘ CBranch RBranch Types
    ASTPredTrans.returnPTS PTBranch = ASTPredTrans.returnPTS PT
    ASTPredTrans.bindPTS PTBranch = ASTPredTrans.bindPTS PT
    ASTPredTrans.opPTS PTBranch (Left  l) x P i =
      ASTPredTrans.opPTS PT l x P i
    ASTPredTrans.opPTS PTBranch (Right (Branching.ASTif gs)) pt P i =
      PTGuards gs pt
      where
      PTGuards :
        (gs : Guards Unit)
        (pt : Level.Lift (Level.# 1) (Fin (lengthGuards gs))
              → ASTPredTrans.PredTrans PT _)
        → Set
      PTGuards (otherwise≔ _) pt =
        pt (Level.lift Fin.zero) P i
      PTGuards (clause (b ≔ c) gs) pt =
          (toBool b ≡ true  → pt (Level.lift Fin.zero) P i)
        × (toBool b ≡ false → PTGuards gs (λ where (Level.lift i) → pt (Level.lift (suc i))))
    ASTPredTrans.opPTS PTBranch (Right (Branching.ASTeither A₁ A₂ e)) pt P i =
        (∀ l → e ≡ Left  l → pt (Level.lift (Left l))  P i)
      × (∀ r → e ≡ Right r → pt (Level.lift (Right r)) P i)
    ASTPredTrans.opPTS PTBranch (Right (Branching.ASTmaybe A₁ m)) pt P i =
        (m ≡ nothing → pt (Level.lift nothing) P i)
      × (∀ j → m ≡ just j → pt (Level.lift (just j)) P i)

    bindPTSUnextendLemma
      : ASTPredTrans.MonoBindPTS PT
        → ∀ {A} (x : AST Cₘ Rₘ CBranch RBranch A)
        → ASTPredTrans._⊑_ PT
            (ASTPredTrans.ptAST PTBranch x)
            (ASTPredTrans.ptAST PT (unextendBranch x))
    bindPTSUnextendLemma mono {A} (ASTreturn x) P i wp = wp
    bindPTSUnextendLemma mono {A} (ASTbind c x f) P i wp =
      let ih = bindPTSUnextendLemma mono x _ i wp
      in {!!}
      where
      foo : ∀ o
            → ASTPredTrans.bindPTS PT c
                (λ x' → ASTPredTrans.ptAST PTBranch (f x'))
                i P o
            → ASTPredTrans.bindPTS PT c
                (λ x' → ASTPredTrans.ptAST PT (unextendBranch (f x')))
                i P o
      foo o ih =
        mono
          (λ x' → ASTPredTrans.ptAST PTBranch (f x'))
          (λ x' → ASTPredTrans.ptAST PT (unextendBranch (f x')))
          (λ x' → bindPTSUnextendLemma mono (f x'))
          c i P o ih
    bindPTSUnextendLemma mono {A} (ASTop c f) P i wp = {!!}


  module Sufficient (Types : ASTOpSemTypes)
    (OS : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types)
    (PT : ASTPredTrans Cₘ Rₘ Cₒ Rₒ Types)
    (SU : ASTSufficientPre Cₘ Rₘ Cₒ Rₒ Types OS PT) where

    open OpSem Types OS
    open PT Types PT

    SufBranch : ASTSufficientPre Cₘ Rₘ CBranch RBranch Types OSBranch PTBranch
    ASTSufficientPre.returnSuf SufBranch x wp =
      ASTSufficientPre.returnSuf SU x wp
    ASTSufficientPre.bindSuf SufBranch{A}{B} c m f ih P i bp =
      ASTSufficientPre.bindSuf SU c (unextendBranch m) (unextendBranch ∘ f)
        {!!} P i {!!}
      where
      pt₁ pt₂ : ∀ {B} → AST Cₘ Rₘ CBranch RBranch B
                → ASTPredTrans.PredTrans PT B
      pt₁ x' = ASTPredTrans.ptAST PTBranch x'

      pt₂ x' = ASTPredTrans.ptAST PT (unextendBranch x')

      lem : ∀ {B} x' → ASTPredTrans._⊑_ PT (pt₁{B} x') (pt₂ x')
      lem (ASTreturn x) P i pf = pf
      lem (ASTbind c x' f) P i pf =
        lem x' {!!} i {!!}
      lem (ASTop c f) P i pf = {!!}

    ASTSufficientPre.opSuf SufBranch = {!!}

-- --   module Sufficient (Types : ASTOpSemTypes)
-- --     (interpOS : ASTOpSem C R Types) (interpPT : ASTPredTrans C R Types)
-- --     (suf : ASTWeakestPre C R Types interpOS interpPT)
-- --     where

-- --     -- open ASTOpSem      interpOS
-- --     -- open OpSem         interpOS
-- --     -- open ASTPredTrans  interpPT
-- --     -- open PT            interpPT
-- --     -- open ASTWeakestPre suf

-- --     -- BranchExtendWeakestPre :
-- --     --   ASTWeakestPre CBranch RBranch BranchExtendOpSem BranchExtendPredTrans
-- --     -- ASTWeakestPre.runM     BranchExtendWeakestPre = runM
-- --     -- ASTWeakestPre.returnPT BranchExtendWeakestPre = returnPT

-- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTreturn x) f wp ih = {!!}
-- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTbind m x) f wp ih = {!!}
-- --     -- ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTop c x) f wp ih = {!!}

-- --     -- ASTWeakestPre.opPT     BranchExtendWeakestPre = {!!}
