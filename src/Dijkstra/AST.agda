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

record MonadAST
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
open MonadAST ⦃ ... ⦄ public
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


module TrivASTBind where
  Cₘ : Set
  Cₘ = Unit

  Rₘ : Cₘ → Set → Set
  Rₘ _ = id

module SimpleASTOpSem
  (Cₘ : Set) (Rₘ : Cₘ → Set → Set)
  (Cₒ : Set → Set₁) (Rₒ : (A : Set) (c : Cₒ A) → Set₁)
  (Types : ASTOpSemTypes)
  (monadOp : MonadAST Cₘ Rₘ Cₒ Rₒ λ A → ASTOpSemTypes.Input Types → ASTOpSemTypes.Output Types A) where

  OS : ASTOpSem Cₘ Rₘ Cₒ Rₒ Types
  ASTOpSem.impl OS = MonadAST.impl monadOp
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
  
  field
    returnPTS : ∀ {A} → A → PredTrans A
    bindPTS   : ∀ {A B} → (c : Cₘ) (f : A → PredTrans B) (i : Input) (P : Post B) → Post (Rₘ c A)
    opPTS     : ∀ {A} → (c : Cₒ A) → (Rₒ A c → PredTrans A) → PredTrans A

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

  monadAST : MonadAST TrivASTBind.Cₘ TrivASTBind.Rₘ C R M
  MonadAST.ret monadAST x (ev , st) = x , st , []
  MonadAST.bind monadAST _ m f i@(ev , st₀) =
    let (x₁ , st₁ , outs₁) = m i
        (x₂ , st₂ , outs₂) = f x₁ (ev , st₁)
    in  (x₂ , st₂ , outs₁ ++ outs₂)
  MonadAST.op monadAST (RWSgets g) _ i@(ev , st) =
    g st , st , []
  MonadAST.op monadAST (RWSputs p refl) _ i@(ev , st) =
    unit , p st , []
  MonadAST.op monadAST (RWSask refl) _ i@(ev , st) =
    ev , st , []
  MonadAST.op monadAST (RWSlocal l) f i@(ev , st) =
    f (Level.lift tt) (l ev , st)
  MonadAST.op monadAST (RWStell outs refl) _ i@(ev , st) =
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

-- --   RWSWeakestPre : ASTWeakestPre C R SimpleRWS.Types RWSOpSem RWSPredTrans
-- --   ASTWeakestPre.returnPT RWSWeakestPre x pt = pt
-- --   ASTWeakestPre.bindPT RWSWeakestPre (ev , pre) m f wp suf
-- --     with ASTOpSem.runAST RWSOpSem m (ev , pre)
-- --   ... | (x₁ , st₁ , outs₁) =
-- --     suf _ x₁ (ev , st₁) (wp x₁ refl)
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSgets g) f x P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSputs p refl) f x P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSask refl) f x P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSlocal l) f suf P (ev , pre) wp =
-- --     let (x₁ , st₁ , outs₁) = ASTOpSem.runAST RWSOpSem (f (Level.lift tt)) (l ev , pre)
-- --     in suf P (l ev , pre) (Level.lift tt) (wp (l ev) refl)
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWStell outs refl) f x P i wp = wp

-- -- module Branching where
-- --   data C (A : Set) : Set₁ where
-- --     ASTif : Guards Unit → C A
-- --     ASTeither : (A₁ A₂ : Set) → Either A₁ A₂ → C A
-- --     ASTmaybe  : (A₁ : Set) → Maybe A₁ → C A

-- --   R : (A : Set) (c : C A) → Set₁
-- --   R A (ASTif gs) = Level.Lift _ (Fin (lengthGuards gs))
-- --   R A (ASTeither A₁ A₂ _) = Level.Lift _ (Either A₁ A₂)
-- --   R A (ASTmaybe A₁ _)     = Level.Lift _ (Maybe A₁)

-- -- module BranchExtend
-- --   (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
-- --   where

-- --   CBranch : Set → Set₁
-- --   CBranch A = Either (C A) (Branching.C A)

-- --   RBranch : (A : Set) (c : CBranch A) → Set₁
-- --   RBranch A (Left x) = R A x
-- --   RBranch A (Right y) = Branching.R A y

-- --   -- mutual

-- --   unextendGuards
-- --     : ∀ {A} (gs : Guards{b = Level.zero} Unit)
-- --         (f : Level.Lift (Level.suc (Level.zero)) (Fin (lengthGuards gs)) → AST C R A)
-- --       → AST C R A
-- --   unextendGuards (otherwise≔ x) f = f (Level.lift zero)
-- --   unextendGuards (clause (b ≔ c) gs) f
-- --     with toBool b
-- --   ... | false = unextendGuards gs (λ where (Level.lift i) → f (Level.lift (suc i)))
-- --   ... | true = f (Level.lift zero)

-- --   unextendBranch : ∀ {A} → AST CBranch RBranch A → AST C R A
-- --   unextendBranch (ASTreturn x) = ASTreturn x
-- --   unextendBranch (ASTbind p f) = ASTbind (unextendBranch p) λ x → unextendBranch (f x)
-- --   unextendBranch (ASTop (Left x) f) = ASTop x (λ r → unextendBranch (f r))
-- --   unextendBranch (ASTop (Right (Branching.ASTif x)) f) =
-- --     unextendGuards x λ i → unextendBranch (f i)
-- --   unextendBranch (ASTop (Right (Branching.ASTeither A₁ A₂ x)) f) =
-- --     unextendBranch (f (Level.lift x))
-- --   unextendBranch (ASTop (Right (Branching.ASTmaybe A₁ x)) f) =
-- --     unextendBranch (f (Level.lift x))

-- --   module OpSem (Types : ASTOpSemTypes) (interp : ASTOpSem C R Types) where

-- --     BranchExtendOpSemImpl : ASTOpSemImpl CBranch RBranch
-- --     ASTOpSemImpl.M BranchExtendOpSemImpl = ASTOpSem.M interp
-- --     ASTOpSemImpl.monadM BranchExtendOpSemImpl = ASTOpSem.monadM interp
-- --     ASTOpSemImpl.opM BranchExtendOpSemImpl (Left c) f =
-- --       ASTOpSem.opM interp c f
-- --     ASTOpSemImpl.opM BranchExtendOpSemImpl (Right y) f = {!!}
-- --     -- ASTOpSemImpl.opM BranchExtendOpSemImpl (Left x) f = ASTOpSem.opM interp x f
-- --     -- ASTOpSemImpl.opM BranchExtendOpSemImpl (Right (Branching.ASTif gs)) f =
-- --     --   interpGuards gs f
-- --     -- ASTOpSemImpl.opM BranchExtendOpSemImpl (Right (Branching.ASTeither A₁ A₂ x)) f =
-- --     --   f (Level.lift x)
-- --     -- ASTOpSemImpl.opM BranchExtendOpSemImpl (Right (Branching.ASTmaybe A₁ x)) f =
-- --     --   f (Level.lift x)

-- --     -- BranchExtendOpSem : ASTOpSem CBranch RBranch Types
-- --     -- ASTOpSem.impl BranchExtendOpSem = BranchExtendOpSemImpl
-- --     -- ASTOpSem.runM BranchExtendOpSem = ASTOpSem.runM interp
-- --     -- ASTOpSem.runMIdLeft BranchExtendOpSem x f i =
-- --     --   ASTOpSem.runMIdLeft interp x {!!} {!!}
-- --     -- ASTOpSem.runMIdRight BranchExtendOpSem = xxx
-- --     --   where postulate xxx : _
-- --     -- ASTOpSem.runMAssoc BranchExtendOpSem = xxx
-- --     --   where postulate xxx : _

-- --   module PT (Types : ASTOpSemTypes) (interp : ASTPredTrans C R Types) where
-- --     open ASTPredTrans interp

-- --     interpGuards : ∀ {A} → (gs : Guards{b = Level.zero} Unit) → (Level.Lift (Level.suc Level.0ℓ) (Fin (lengthGuards gs)) → PredTrans A) 
-- --                    → PredTrans A
-- --     interpGuards (otherwise≔ c) ih P i =
-- --       ih (Level.lift Fin.zero) P i
-- --     interpGuards (clause (b ≔ c) gs) ih P i =
-- --         (toBool b ≡ true  → ih (Level.lift Fin.zero) P i)
-- --       × (toBool b ≡ false →
-- --         interpGuards gs (λ where (Level.lift i) → ih (Level.lift (Fin.suc i))) P i)

-- --     -- BranchExtendPredTrans : ASTPredTrans CBranch RBranch Types
-- --     -- ASTPredTrans.Input     BranchExtendPredTrans = Input
-- --     -- ASTPredTrans.Output    BranchExtendPredTrans = Output
-- --     -- ASTPredTrans.returnPTS BranchExtendPredTrans = returnPTS
-- --     -- ASTPredTrans.bindPTS   BranchExtendPredTrans = bindPTS
-- --     -- ASTPredTrans.opPTS BranchExtendPredTrans (Left c) ih P i =
-- --     --   opPTS c ih P i
-- --     -- ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTif gs)) ih P i =
-- --     --   interpGuards gs ih P i
-- --     -- ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTeither A₁ A₂ e)) ih P i =
-- --     --     (∀ x → (e ≡ Left x ) → ih (Level.lift (Left  x)) P i)
-- --     --   × (∀ y → (e ≡ Right y) → ih (Level.lift (Right y)) P i)
-- --     -- ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTmaybe A₁ m)) ih P i =
-- --     --     m ≡ nothing → ih (Level.lift nothing) P i
-- --     --   × (∀ x → m ≡ just x → ih (Level.lift (just x)) P i)


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
