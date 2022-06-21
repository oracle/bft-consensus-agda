{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
module Dijkstra.AST.Branching where

open import Dijkstra.AST.Core
open import Dijkstra.AST.Prelude

data BranchCmd (A : Set) : Set₁ where
  BCif     :               Bool       → BranchCmd A
  BCeither : {B C : Set} → Either B C → BranchCmd A
  BCmaybe  : {B   : Set} → Maybe  B   → BranchCmd A

BranchSubArg : {A : Set} → BranchCmd A → Set₁
BranchSubArg (BCif           x) = Lift _ Bool
BranchSubArg (BCeither{B}{C} x) = Lift _ (Either B C)
BranchSubArg (BCmaybe {B}    x) = Lift _ (Maybe  B)

BranchSubRet : {A : Set} {c : BranchCmd A} → BranchSubArg c → Set
BranchSubRet{A} {BCif     x} _ = A
BranchSubRet{A} {BCeither x} _ = A
BranchSubRet{A} {BCmaybe  x} _ = A

module ASTExtension (O : ASTOps) where
  open ASTOps

  BranchOps : ASTOps
  Cmd  BranchOps A = Either (Cmd O A) (BranchCmd A)
  SubArg BranchOps{_} (Left x)    = SubArg O x
  SubArg BranchOps{_} (Right y)   = BranchSubArg y
  SubRet BranchOps{_} {Left x}  r = SubRet O r
  SubRet BranchOps{_} {Right y} r = BranchSubRet r

  unextend : ∀ {A} → AST BranchOps A → AST O A
  unextend (ASTreturn x)      = ASTreturn x
  unextend (ASTbind m f)      = ASTbind (unextend m) (unextend ∘ f)
  unextend (ASTop (Left c) f) = ASTop c (unextend ∘ f)
  unextend (ASTop (Right (BCif false))         f) = unextend (f (lift false))
  unextend (ASTop (Right (BCif true))          f) = unextend (f (lift true))
  unextend (ASTop (Right (BCeither (Left x)))  f) = unextend (f (lift (Left x)))
  unextend (ASTop (Right (BCeither (Right y))) f) = unextend (f (lift (Right y)))
  unextend (ASTop (Right (BCmaybe nothing))    f) = unextend (f (lift nothing))
  unextend (ASTop (Right (BCmaybe (just x)))   f) = unextend (f (lift (just x)))

module OpSemExtension {O : ASTOps} {T : ASTTypes} (OpSem : ASTOpSem O T) where
  open ASTExtension O
  open ASTOpSem

  BranchOpSem : ASTOpSem BranchOps T
  runAST BranchOpSem m i = runAST OpSem (unextend m) i

module PredTransExtension {O : ASTOps} {T : ASTTypes} (PT : ASTPredTrans O T) where
  open ASTExtension O
  open ASTPredTrans

  BranchPT : ASTPredTrans BranchOps T
  returnPT BranchPT          = returnPT PT
  bindPT   BranchPT          = bindPT   PT
  opPT     BranchPT (Left x) =
    opPT PT x
  opPT     BranchPT (Right (BCif c))     f P i =
      (       c ≡ true    → f (lift true)      P i)
    × (       c ≡ false   → f (lift false)     P i)
  opPT     BranchPT (Right (BCeither e)) f P i =
      (∀ l →  e ≡ Left  l → f (lift (Left l))  P i)
    × (∀ r →  e ≡ Right r → f (lift (Right r)) P i)
  opPT     BranchPT (Right (BCmaybe mb)) f P i =
      (      mb ≡ nothing → f (lift nothing)   P i)
    × (∀ j → mb ≡ just j  → f (lift (just j))  P i)
  open ASTPredTrans BranchPT

module PredTransExtensionMono
  {O : ASTOps} {T : ASTTypes} {PT : ASTPredTrans O T}
  (M : ASTPredTransMono PT) where
  open ASTTypes T hiding (Exec)
  open ASTExtension O
  open PredTransExtension PT
  open ASTPredTrans
  open ASTPredTransMono

  module M where
    open ASTPredTransMono M public

  BranchPTMono : ASTPredTransMono BranchPT
  returnPTMono BranchPTMono          = M.returnPTMono
  bindPTMono   BranchPTMono          = M.bindPTMono
  opPTMono     BranchPTMono (Left x) = M.opPTMono x
  proj₁ (opPTMono BranchPTMono (Right (BCif x))       f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p)   refl =
    f₁⊑f₂ (lift true)      _ i (mono₁ (lift true)      _ _ P₁⊆P₂ i (proj₁ p refl))
  proj₂ (opPTMono BranchPTMono (Right (BCif x))       f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p)   refl =
    f₁⊑f₂ (lift false)     _ i (mono₁ (lift false)     _ _ P₁⊆P₂ i (proj₂ p refl))
  proj₁ (opPTMono BranchPTMono (Right (BCeither x))   f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p) l refl =
    f₁⊑f₂ (lift (Left l))  _ i (mono₁ (lift (Left l))  _ _ P₁⊆P₂ i (proj₁ p l refl))
  proj₂ (opPTMono BranchPTMono (Right (BCeither x))   f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p) r refl =
    f₁⊑f₂ (lift (Right r)) _ i (mono₁ (lift (Right r)) _ _ P₁⊆P₂ i (proj₂ p r refl))
  proj₁ (opPTMono BranchPTMono (Right (BCmaybe x))    f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p)   refl =
    f₁⊑f₂ (lift nothing)   _ i (mono₁ (lift nothing)   _ _ P₁⊆P₂ i (proj₁ p refl))
  proj₂ (opPTMono BranchPTMono (Right (BCmaybe x))    f₁ f₂ mono₁ mono₂ f₁⊑f₂ P₁ P₂ i P₁⊆P₂ p) j refl =
    f₁⊑f₂ (lift (just j))  _ i (mono₁ (lift (just j))  _ _ P₁⊆P₂ i (proj₂ p j refl))

  unextendPT : ∀ {A} (m : AST BranchOps A)
               → predTrans BranchPT m ⊑ predTrans PT (unextend m)
  unextendPT (ASTreturn x)                          P i   wp = wp
  unextendPT (ASTbind m f)                          P i   wp =
    predTransMono M (unextend m) _ _
      (M.bindPTMono _ _
        (predTransMono BranchPTMono ∘ f) (M.predTransMono ∘ unextend ∘ f)
        (unextendPT ∘ f)
        i _ _ (λ _ x → x))
      i (unextendPT m _ _ wp)
  unextendPT (ASTop (Left x)                     f) P i   wp =
    M.opPTMono x _ _
      (predTransMono BranchPTMono ∘ f)
      (M.predTransMono ∘ unextend ∘ f)
      (unextendPT ∘ f) _ _ i (λ _ x → x) wp
  unextendPT (ASTop (Right (BCif false))         f) P i   wp =
    unextendPT (f (lift false))     P i (proj₂ wp refl)
  unextendPT (ASTop (Right (BCif true))          f) P i   wp =
    unextendPT (f (lift true))      _ _ (proj₁ wp refl)
  unextendPT (ASTop (Right (BCeither (Left x)))  f) P i   wp =
    unextendPT (f (lift (Left x)))  _ _ (proj₁ wp _ refl)
  unextendPT (ASTop (Right (BCeither (Right y))) f) P i wp =
    unextendPT (f (lift (Right y))) _ _ (proj₂ wp _ refl)
  unextendPT (ASTop (Right (BCmaybe nothing))    f) P i wp =
    unextendPT (f (lift nothing))   _ _ (proj₁ wp   refl)
  unextendPT (ASTop (Right (BCmaybe (just j)))   f) P i wp =
    unextendPT (f (lift (just j)))  _ _ (proj₂ wp _ refl)

  extendPT : ∀ {A} (m : AST BranchOps A)
             → predTrans PT (unextend m) ⊑ predTrans BranchPT m
  extendPT (ASTreturn x)                         P i wp = wp
  extendPT (ASTbind m f)                         P i wp =
    predTransMono BranchPTMono m _ _
    (bindPTMono BranchPTMono _ _
      (M.predTransMono ∘ unextend ∘ f) (predTransMono BranchPTMono ∘ f) (extendPT ∘ f)
      i _ _ (λ _ x → x))
      _
      (extendPT m _ _ wp)
  extendPT (ASTop (Left x) f) P i wp =
    opPTMono BranchPTMono (Left x) _ _
      (M.predTransMono ∘ unextend ∘ f) (predTransMono BranchPTMono ∘ f) (extendPT ∘ f)
      _ _ i (λ _ x → x) wp
  proj₁ (extendPT (ASTop (Right (BCif x))     f) P i wp)   refl =
    extendPT (f (lift true))      _ _ wp
  proj₂ (extendPT (ASTop (Right (BCif x))     f) P i wp)   refl =
    extendPT (f (lift false))     _ _ wp
  proj₁ (extendPT (ASTop (Right (BCeither x)) f) P i wp) l refl =
    extendPT (f (lift (Left l)))  _ _ wp
  proj₂ (extendPT (ASTop (Right (BCeither x)) f) P i wp) r refl =
    extendPT (f (lift (Right r))) _ _ wp
  proj₁ (extendPT (ASTop (Right (BCmaybe x))  f) P i wp)   refl =
    extendPT (f (lift nothing))   _ _ wp
  proj₂ (extendPT (ASTop (Right (BCmaybe x))  f) P i wp) j refl =
    extendPT (f (lift (just j)))  _ _ wp

module SufficientExtension
  {O} {T} {OS : ASTOpSem O T} {PT : ASTPredTrans O T}
  (M : ASTPredTransMono PT) (S : ASTSufficientPT OS PT) where
  open ASTTypes T
  open ASTExtension O
  open ASTPredTrans
  open ASTSufficientPT
  open ASTTypes T
  open OpSemExtension OS
  open PredTransExtension PT
  open PredTransExtensionMono M

  BranchSuf : ASTSufficientPT BranchOpSem BranchPT
  returnSuf BranchSuf = returnSuf S
  bindSuf BranchSuf m f mSuf fSuf P i wp =
    bindSuf S (unextend m) (unextend ∘ f) mSuf' fSuf' _ _ wp'
    where
    mSuf' : Sufficient S _ (unextend m)
    mSuf' P i wp = mSuf _ _ (extendPT m _ _ wp)

    fSuf' : ∀ x → Sufficient S _ (unextend (f x))
    fSuf' x P i wp = fSuf x _ _ (extendPT (f x) _ _ wp)

    wp' : predTrans PT (ASTbind (unextend m) (unextend ∘ f)) P i
    wp' = unextendPT (ASTbind m f) _ _ wp
  opSuf BranchSuf (Left x)                     f fSuf P i wp =
    opSuf S x (unextend ∘ f) fSuf' _ _ wp'
    where
    fSuf' : ∀ r → Sufficient S _ (unextend (f r))
    fSuf' r P i wp = fSuf r _ _ (extendPT (f r) _ _ wp)

    wp' : predTrans PT (ASTop x (unextend ∘ f)) _ _
    wp' = unextendPT (ASTop (Left x) f) _ _ wp
  opSuf BranchSuf (Right (BCif false))         f fSuf P i wp =
    fSuf (lift false)     _ _ (proj₂ wp   refl)
  opSuf BranchSuf (Right (BCif true))          f fSuf P i wp =
    fSuf (lift true)      _ _ (proj₁ wp   refl)
  opSuf BranchSuf (Right (BCeither (Left x)))  f fSuf P i wp =
    fSuf (lift (Left x))  _ _ (proj₁ wp _ refl)
  opSuf BranchSuf (Right (BCeither (Right y))) f fSuf P i wp =
    fSuf (lift (Right y)) _ _ (proj₂ wp _ refl)
  opSuf BranchSuf (Right (BCmaybe nothing))    f fSuf P i wp =
    fSuf (lift nothing)   _ _ (proj₁ wp   refl)
  opSuf BranchSuf (Right (BCmaybe (just j)))   f fSuf P i wp =
    fSuf (lift (just j))  _ _ (proj₂ wp _ refl)

module BranchingSyntax (BaseOps : ASTOps) where

  Ops = ASTExtension.BranchOps BaseOps

  ifAST_then_else : ∀ {A} → Bool → (t e : AST Ops A) → AST Ops A
  ifAST b then t else e = ASTop (Right (BCif b))
                                λ { (lift true)  → t
                                  ; (lift false) → e
                                  }

  maybeAST :  ∀ {A B : Set}
              → (A → AST Ops B)
              → AST Ops B
              → Maybe A
              → AST Ops B
  maybeAST fA B mA = ASTop (Right (BCmaybe mA))
                           λ { (lift nothing)  → B
                             ; (lift (just a)) → fA a
                             }

  eitherAST : ∀ {A B C : Set}
              → (A → AST Ops C)
              → (B → AST Ops C)
              → Either A B
              → AST Ops C
  eitherAST fA fB eAB = ASTop (Right (BCeither eAB))
                              λ { (lift (Left  a)) → fA a
                                ; (lift (Right b)) → fB b
                                }

  -- Same but with arguments in more "natural" order
  eitherSAST : ∀ {A B C : Set}
               → Either A B
               → (A → AST Ops C)
               → (B → AST Ops C)
               → AST Ops C
  eitherSAST eAB fA fB = eitherAST fA fB eAB

module ConditionalExtensions
  {BaseOps    : ASTOps}
  {BaseTypes  : ASTTypes}
  (BasePT     : ASTPredTrans BaseOps BaseTypes)
  (BaseOpSem  : ASTOpSem BaseOps BaseTypes)
  (BasePTMono : ASTPredTransMono BasePT)
  (BaseSuf    : ASTSufficientPT BaseOpSem BasePT)
  where
  ExtOps = ASTExtension.BranchOps BaseOps
  ExtAST = AST ExtOps
  PT     = PredTransExtension.BranchPT BasePT
  runAST = ASTOpSem.runAST (OpSemExtension.BranchOpSem BaseOpSem)
  PTMono = PredTransExtensionMono.BranchPTMono BasePTMono
  Suf    = SufficientExtension.BranchSuf BasePTMono BaseSuf
  open ASTOps BaseOps             public
  open ASTTypes BaseTypes         public
  open ASTSufficientPT Suf        public
  open ASTPredTrans PT            public
  open ASTPredTransMono PTMono    public
  open BranchingSyntax BaseOps    public

  open ASTPTIWeakest BaseOpSem BasePT

  module WithPTIWBase (predTrans-is-weakest-base : ∀ {A i} → (m : AST BaseOps A) → Post⇒wp-base m i) where

    Post⇒wp : ∀ {A} → ExtAST A → Input → Set₁
    Post⇒wp {A} m i =
      (P : Post A)
      → P (runAST m i)
      → predTrans m P i

    open ASTExtension BaseOps
    open PredTransExtensionMono BasePTMono

    -- We use unextend to get an equivalent AST without branching operations, use the provided proof
    -- that predTrans is weakest for the underlying AST, and then use extendPT to extend that
    -- property to the AST with branching operatiions.
    predTrans-is-weakest : ∀ {A i} → (m : ExtAST A) → Post⇒wp m i
    predTrans-is-weakest {i = i} m P Pr =
      extendPT m P i (predTrans-is-weakest-base (unextend m) P Pr)

