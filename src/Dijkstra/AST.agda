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

data AST (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set → Set₁ where
  -- monadic operations
  ASTreturn : ∀ {A} → A → AST C R A
  ASTbind   : ∀ {A B} → AST C R A → (A → AST C R B) → AST C R B
  -- effect operations
  ASTop : ∀ {A} → (c : C A) → (R A c → AST C R A) → AST C R A

record ASTOpSemTypes : Set₁ where
  constructor mkASTOpSemTypes
  field
    Input  : Set
    Output : Set → Set

record ASTOpSemImpl (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₁ where
  constructor mkASTOpSemImpl
  field
    -- Implementation
    M          : Set → Set
    ⦃ monadM ⦄ : Monad M
    opM        : ∀ {A} → (c : C A) → (R A c → M A) → M A

  runAST : ∀ {A} → AST C R A → M A
  runAST (ASTreturn x) = return x
  runAST (ASTbind p f) = runAST p >>= λ x → runAST (f x)
  runAST (ASTop c f) = opM c (λ x → runAST (f x))


record ASTOpSem (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₁ where
  constructor mkASTOpSem
  field
    IO : ASTOpSemTypes
  open ASTOpSemTypes IO public
  field
    impl : ASTOpSemImpl C R
  open ASTOpSemImpl impl public
  field
    runM : ∀ {A} → M A → Input → Output A

  -- Coherence
    runMIdLeft  : ∀ {A} (x : A) (f : A → AST C R A) (i : Input)
                  →   runM (runAST (ASTbind (ASTreturn x) f)) i
                    ≡ runM (runAST (f x)) i
    runMIdRight : ∀ {A} (m : AST C R A) (i : Input)
                  →   runM (runAST (ASTbind m ASTreturn)) i
                    ≡ runM (runAST m) i
    runMAssoc   : ∀ {A B₁ B₂} (m : AST C R A) (f : A → AST C R B₁) (g : B₁ → AST C R B₂) (i : Input)
                  →   runM (runAST (ASTbind (ASTbind m f) g)) i
                    ≡ runM (runAST (ASTbind m (λ x → ASTbind (f x) g))) i


module SimpleASTOpSem
  (I : Set) (O : Set → Set)
  where

  M : Set → Set
  M A = I → O A

  module _
    (m : Monad M) (ml : MonadLaws M ⦃ m ⦄) where

    os : ∀ {C R} → (opM : ∀ {A} → (c : C A) → (R A c → M A) → M A)
         → ASTOpSem C R
    ASTOpSemTypes.Input (ASTOpSem.IO (os opM)) = I
    ASTOpSemTypes.Output (ASTOpSem.IO (os opM)) = O
    ASTOpSemImpl.M (ASTOpSem.impl (os opM)) = M
    ASTOpSemImpl.monadM (ASTOpSem.impl (os opM)) = m
    ASTOpSemImpl.opM (ASTOpSem.impl (os opM)) = opM
    ASTOpSem.runM (os opM) = id
    ASTOpSem.runMIdLeft (os opM) x f i =
      {!MonadLaws.idLeft ⦃ m = m ⦄ ml x ?!}
    ASTOpSem.runMIdRight (os opM) = {!!}
    ASTOpSem.runMAssoc (os opM) = {!!}


  -- runM : ∀ {A} → M A → I → O A
  -- runM m = m

  -- impl : ⦃ _ : Monad O ⦄ → ASTOpSemImpl C R
  -- ASTOpSemImpl.M impl = M
  -- Monad.return (ASTOpSemImpl.monadM impl) x i = return x
  -- Monad._>>=_ (ASTOpSemImpl.monadM impl) m f i =
  --   let o = m i
  --   in o >>= λ x → f x (step o)
  -- ASTOpSemImpl.opM impl = {!!}

  -- opSem : ⦃ _ : Monad O ⦄ → (ml : MonadLaws O) → ASTOpSem C R
  -- ASTOpSemTypes.Input (ASTOpSem.IO (opSem ml)) = I
  -- ASTOpSemTypes.Output (ASTOpSem.IO (opSem ml)) = O
  -- ASTOpSem.impl (opSem ml) = impl
  -- ASTOpSem.runM (opSem ml) = runM
  -- ASTOpSem.runMIdLeft (opSem ml) x f i
  --   =   (return x >>= λ y → ASTOpSemImpl.runAST impl (f y) (step (return x)))
  --     ≡ {!!} ∋ {!!}
  -- ASTOpSem.runMIdRight (opSem ml) = {!!}
  -- ASTOpSem.runMAssoc (opSem ml) = {!!}

-- simpleASTOpSem : ∀ {C R} → ASTOpSemTypes C R → ASTOpSem C R
-- ASTOpSem.IO (simpleASTOpSem x) = x
-- ASTOpSemImpl.M (ASTOpSem.impl (simpleASTOpSem x)) =
--   λ A → ASTOpSemTypes.Input x → ASTOpSemTypes.Output x A
-- ASTOpSemImpl.monadM (ASTOpSem.impl (simpleASTOpSem x)) = {!!}
-- ASTOpSemImpl.opM (ASTOpSem.impl (simpleASTOpSem x)) = {!!}
-- ASTOpSem.runM (simpleASTOpSem x) = {!!}
-- ASTOpSem.runMLaw1 (simpleASTOpSem x) = {!!}

-- -- record ASTPredTrans (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁) : Set₂ where
-- --   constructor mkASTPredTrans
-- --   field
-- --     Input  : Set
-- --     Output : Set → Set

-- --   Pre : Set₁
-- --   Pre = Input → Set

-- --   Post : Set → Set₁
-- --   Post A = Output A → Set

-- --   PredTrans : (A : Set) → Set₁
-- --   PredTrans A = Post A → Pre
  
-- --   field
-- --     returnPTS : ∀ {A} → A → PredTrans A
-- --     bindPTS   : ∀ {A B} → (A → PredTrans B) → Post B → Input → Post A
-- --     opPTS     : ∀ {A} → (c : C A) → (R A c → PredTrans A) → PredTrans A

-- --   ptAST : ∀ {A} → AST C R A → PredTrans A
-- --   ptAST (ASTreturn x) = returnPTS x
-- --   ptAST (ASTbind p f) Post input =
-- --     ptAST p (bindPTS (λ x → ptAST (f x)) Post input) input
-- --   ptAST (ASTop c f) Post = opPTS c (λ r → ptAST (f r)) Post

-- -- record ASTWeakestPre
-- --   (C : Set → Set₁) (R : (A : Set) (c : C A) → Set₁)
-- --   (os : ASTOpSem C R) (pt : ASTPredTrans C R) : Set₁ where
-- --   constructor mkASTWeakestPre
-- --   open ASTOpSem     os
-- --   open ASTPredTrans pt
-- --   field
-- --     runM : ∀ {A} → M A → Input → Output A

-- --   Sufficient : (A : Set) (m : AST C R A) (P : Post A) (i : Input) → Set
-- --   Sufficient A m P i =
-- --     ptAST m P i → P (runM (runAST m) i)

-- --   field
-- --     returnPT : ∀ {A} (x : A) {P} {i} → Sufficient A (ASTreturn x) P i
-- --     bindPT   : ∀ {A B P} i (m : AST C R A) (f : A → AST C R B)
-- --                → (wp : bindPTS (λ x → ptAST (f x)) P i (runM (runAST m) i))
-- --                → (∀ x i' → Sufficient B (f x) P i')
-- --                → P (runM (runAST (ASTbind m f)) i)
-- --     opPT     : ∀ {A} (c : C A) (f : R A c → AST C R A)
-- --                → ((P : Post A) (i : Input) (r : R A c) → Sufficient A (f r) P i)
-- --                → (P : Post A) (i : Input)
-- --                → opPTS c (λ r → ptAST (f r)) P i
-- --                → P (runM (runAST (ASTop c f)) i)
-- --                -- Sufficient A (ASTOp c f) P i
-- --                -- → (m : AST C R A) (f : A → AST C R B)
-- --                -- → Sufficient A m (bindPTS (λ x → ptAST (f x)) P i) i
-- --                -- → (∀ x i' → Sufficient B (f x) P i')
-- --                -- → Sufficient B (ASTbind m f) P i

-- --   sufficient : ∀ {A} → (m : AST C R A) (P : Post A) (i : Input) → Sufficient A m P i
-- --   sufficient (ASTreturn x) P i wp = returnPT x wp
-- --   sufficient (ASTbind m f) P i wp
-- --     with sufficient m (bindPTS (λ x → ptAST (f x)) P i) i wp
-- --   ... | wp' = bindPT i m f wp' (λ x i' → sufficient (f x) P i')
-- --   sufficient{A} (ASTop c f) P i wp =
-- --     opPT c f ih P i wp
-- --     where
-- --     ih : (P : Post A) (i : Input) (r : R A c) → Sufficient A (f r) P i
-- --     ih P i r = sufficient (f r) P i

-- -- module RWS (Ev Wr St : Set) where

-- --   data C (A : Set) : Set₁ where
-- --     RWSgets  : (St → A) → C A
-- --     RWSputs  : (St → St) → A ≡ Unit → C A
-- --     RWSask   : (A ≡ Ev) → C A
-- --     RWSlocal : (Ev → Ev) → C A
-- --     RWStell  : List Wr → (A ≡ Unit) → C A

-- --   R : (A : Set) (c : C A) → Set₁
-- --   R A (RWSgets x) = Level.Lift _ ⊥
-- --   R .Unit (RWSputs f refl) = Level.Lift _ ⊥
-- --   R .Ev (RWSask refl) = Level.Lift _ ⊥
-- --   R A (RWSlocal x) = Level.Lift _ ⊤
-- --   R A (RWStell x refl) = Level.Lift _ ⊥

-- --   RWSOpSem : ASTOpSem C R
-- --   ASTOpSem.M       RWSOpSem A = (ev : Ev) (st : St) (log : List Wr) → A × St × List Wr
-- --   ASTOpSem.monadM RWSOpSem = {!!}
-- --   -- ASTOpSem.returnI RWSOpSem x ev st log = x , st , log
-- --   -- ASTOpSem.bindI   RWSOpSem x f ev st outs =
-- --   --   let (x₁ , st₁ , outs₁) = x ev st outs
-- --   --       (x₂ , st₂ , outs₂) = f x₁ ev st₁ outs₁
-- --   --   in x₂ , st₂ , outs₂
-- --   ASTOpSem.opM     RWSOpSem (RWSgets g) f ev st outs =
-- --     (g st) , st , outs
-- --   ASTOpSem.opM     RWSOpSem (RWSputs p refl) f ev st outs =
-- --     unit , p st , outs
-- --   ASTOpSem.opM     RWSOpSem (RWSask refl) f ev st outs =
-- --     ev , st , outs
-- --   ASTOpSem.opM     RWSOpSem (RWSlocal l) f ev st outs =
-- --     f (Level.lift _) (l ev) st outs
-- --   ASTOpSem.opM     RWSOpSem (RWStell t refl) f ev st outs =
-- --     unit , st , outs ++ t

-- --   RWSPredTrans : ASTPredTrans C R
-- --   ASTPredTrans.Input RWSPredTrans = Ev × St × List Wr
-- --   ASTPredTrans.Output RWSPredTrans A = A × St × List Wr
-- --   ASTPredTrans.returnPTS RWSPredTrans x Post (ev , pre , outs) =
-- --     Post (x , pre , outs)
-- --   ASTPredTrans.bindPTS RWSPredTrans wp Post (ev , st₀ , outs₀) (x₁ , st₁ , outs₁) =
-- --     ∀ r → r ≡ x₁ → wp r Post (ev , st₁ , outs₁)
-- --   ASTPredTrans.opPTS RWSPredTrans (RWSgets g) _ Post (ev , pre , outs) =
-- --     Post (g pre , pre , outs)
-- --   ASTPredTrans.opPTS RWSPredTrans (RWSputs p refl) x Post (ev , pre , outs) =
-- --     Post (unit , p pre , outs)
-- --   ASTPredTrans.opPTS RWSPredTrans (RWSask refl) _ Post (ev , pre , outs) =
-- --     Post (ev , pre , outs)
-- --   ASTPredTrans.opPTS RWSPredTrans (RWSlocal l) f Post (ev , pre , outs) =
-- --     ∀ ev' → ev' ≡ l ev → f (Level.lift _) Post (l ev , pre , outs)
-- --   ASTPredTrans.opPTS RWSPredTrans (RWStell outs refl) x Post (ev , pre , outs₀) =
-- --     Post (unit , pre , outs₀ ++ outs)

-- --   RWSWeakestPre : ASTWeakestPre C R RWSOpSem RWSPredTrans
-- --   ASTWeakestPre.runM RWSWeakestPre f (ev , pre , outs) = f ev pre outs
-- --   ASTWeakestPre.returnPT RWSWeakestPre x wp = wp
-- --   ASTWeakestPre.bindPT RWSWeakestPre (ev , pre , outs) m f wp suf
-- --     with ASTOpSem.runAST RWSOpSem m ev pre outs
-- --   ... | (x , st₁ , outs₁) =
-- --     suf x (ev , st₁ , outs₁) (wp x refl)
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSgets g) f ih P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSputs p refl) f ih P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSask refl) f ih P i wp = wp
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWSlocal l) f ih P (ev , pre , outs₀) wp =
-- --     ih P ((l ev , pre , outs₀)) (Level.lift tt) (wp _ refl)
-- --   ASTWeakestPre.opPT RWSWeakestPre (RWStell outs refl) f ih P i wp = wp

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

-- --   module OpSem (interp : ASTOpSem C R) where

-- --     interpGuards : ∀ {A : Set} (gs : Guards{b = Level.zero} Unit) (f : Level.Lift (Level.suc Level.zero) (Fin (lengthGuards gs)) → ASTOpSem.M interp A)
-- --                    → ASTOpSem.M interp A
-- --     interpGuards (otherwise≔ x) f = f (Level.lift zero)
-- --     interpGuards (clause (x ≔ x₁) gs) f
-- --       with toBool x
-- --     ... | false = interpGuards gs λ { (Level.lift n) → f (Level.lift (suc n))}
-- --     ... | true = f (Level.lift zero)

-- --     BranchExtendOpSem : ASTOpSem CBranch RBranch
-- --     ASTOpSem.M       BranchExtendOpSem = ASTOpSem.M interp
-- --     ASTOpSem.monadM  BranchExtendOpSem = {!!}
-- --     -- ASTOpSem.returnI BranchExtendOpSem = ASTOpSem.returnI interp
-- --     -- ASTOpSem.bindI   BranchExtendOpSem = ASTOpSem.bindI interp
-- --     ASTOpSem.opM     BranchExtendOpSem (Left c) f = ASTOpSem.opM interp c f
-- --     ASTOpSem.opM     BranchExtendOpSem (Right (Branching.ASTif gs)) f = interpGuards gs f
-- --     ASTOpSem.opM     BranchExtendOpSem (Right (Branching.ASTeither A₁ A₂ x₁)) f = f (Level.lift x₁)
-- --     ASTOpSem.opM     BranchExtendOpSem (Right (Branching.ASTmaybe A₁ x₁)) f = f (Level.lift x₁)

-- --   module PT (interp : ASTPredTrans C R) where
-- --     open ASTPredTrans interp

-- --     interpGuards : ∀ {A} → (gs : Guards{b = Level.zero} Unit) → (Level.Lift (Level.suc Level.0ℓ) (Fin (lengthGuards gs)) → PredTrans A) 
-- --                    → PredTrans A
-- --     interpGuards (otherwise≔ c) ih P i =
-- --       ih (Level.lift Fin.zero) P i
-- --     interpGuards (clause (b ≔ c) gs) ih P i =
-- --         (toBool b ≡ true  → ih (Level.lift Fin.zero) P i)
-- --       × (toBool b ≡ false →
-- --         interpGuards gs (λ where (Level.lift i) → ih (Level.lift (Fin.suc i))) P i)

-- --     BranchExtendPredTrans : ASTPredTrans CBranch RBranch
-- --     ASTPredTrans.Input     BranchExtendPredTrans = Input
-- --     ASTPredTrans.Output    BranchExtendPredTrans = Output
-- --     ASTPredTrans.returnPTS BranchExtendPredTrans = returnPTS
-- --     ASTPredTrans.bindPTS   BranchExtendPredTrans = bindPTS
-- --     ASTPredTrans.opPTS BranchExtendPredTrans (Left c) ih P i =
-- --       opPTS c ih P i
-- --     ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTif gs)) ih P i =
-- --       interpGuards gs ih P i
-- --     ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTeither A₁ A₂ e)) ih P i =
-- --         (∀ x → (e ≡ Left x ) → ih (Level.lift (Left  x)) P i)
-- --       × (∀ y → (e ≡ Right y) → ih (Level.lift (Right y)) P i)
-- --     ASTPredTrans.opPTS BranchExtendPredTrans (Right (Branching.ASTmaybe A₁ m)) ih P i =
-- --         m ≡ nothing → ih (Level.lift nothing) P i
-- --       × (∀ x → m ≡ just x → ih (Level.lift (just x)) P i)


-- --   module Sufficient
-- --     (interpOS : ASTOpSem C R) (interpPT : ASTPredTrans C R)
-- --     (suf : ASTWeakestPre C R interpOS interpPT)
-- --     where

-- --     open ASTOpSem      interpOS
-- --     open OpSem         interpOS
-- --     open ASTPredTrans  interpPT
-- --     open PT            interpPT
-- --     open ASTWeakestPre suf

-- --     BranchExtendWeakestPre :
-- --       ASTWeakestPre CBranch RBranch BranchExtendOpSem BranchExtendPredTrans
-- --     ASTWeakestPre.runM     BranchExtendWeakestPre = runM
-- --     ASTWeakestPre.returnPT BranchExtendWeakestPre = returnPT

-- --     ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTreturn x) f wp ih = {!!}
-- --     ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTbind m x) f wp ih = {!!}
-- --     ASTWeakestPre.bindPT BranchExtendWeakestPre i (ASTop c x) f wp ih = {!!}

-- --     ASTWeakestPre.opPT     BranchExtendWeakestPre = {!!}
