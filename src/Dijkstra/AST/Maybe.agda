{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Maybe where

open import Dijkstra.AST.Prelude

module MaybeBase where

  open import Dijkstra.AST.Core

  data MaybeCmd (C : Set) : Set₁ where
    Maybe-bail : MaybeCmd C

  MaybeSubArg : {C : Set} (c : MaybeCmd C) → Set₁
  MaybeSubArg Maybe-bail = Lift _ Void

  MaybeSubRet : {A : Set} {c : MaybeCmd A} (r : MaybeSubArg c) → Set
  MaybeSubRet {c = Maybe-bail} ()

  open ASTOps
  MaybeOps : ASTOps
  Cmd    MaybeOps = MaybeCmd
  SubArg MaybeOps = MaybeSubArg
  SubRet MaybeOps = MaybeSubRet

  MaybeBaseAST = AST MaybeOps

  module _ where
    open ASTTypes
    MaybeTypes : ASTTypes
    Input  MaybeTypes   = Unit
    Output MaybeTypes A = Maybe A

  open ASTTypes MaybeTypes

  module _ where
    open ASTOpSem
    MaybeOpSem : ASTOpSem MaybeOps MaybeTypes
    runAST MaybeOpSem (ASTreturn x) _ = just x
    runAST MaybeOpSem (ASTbind m f) i
      with runAST MaybeOpSem m i
    ...| nothing = nothing
    ...| just x  = runAST MaybeOpSem (f x) i
    runAST MaybeOpSem (ASTop Maybe-bail f) i = nothing

    runMaybeBase = runAST MaybeOpSem

  MaybebindPost : ∀ {A B} → (A → PredTrans B) → Post B → Post A
  MaybebindPost _ P nothing  = P nothing
  MaybebindPost f P (just y) = f y P unit

  MaybebindPost⊆
    : ∀ {A B} (f : A → PredTrans B) (P₁ : Post B) (P₂ : Post A)
      → (P₁ nothing → P₂ nothing)
      → (∀ x → f x P₁ unit → P₂ (just x))
      → MaybebindPost f P₁ ⊆ₒ P₂
  MaybebindPost⊆ f P₁ P₂ n⊆ j⊆ nothing wp = n⊆ wp
  MaybebindPost⊆ f P₁ P₂ n⊆ j⊆ (just x) wp = j⊆ x wp

  open ASTPredTrans
  MaybePT : ASTPredTrans MaybeOps MaybeTypes
  returnPT MaybePT x P i               = P (just x)
  -- Note that it is important *not* to pattern match the input as 'unit'.  Even though this is the
  -- only constructor for Unit, Agda does not figure out that this case applies to a general Input
  -- (because Input is of type Unit), and therefore does not expand this case when encountering
  -- bindPT.
  bindPT   MaybePT f i Post x          = ∀ r → r ≡ x → MaybebindPost f Post r
  opPT     MaybePT Maybe-bail f Post i = Post nothing

  ------------------------------------------------------------------------------
  open ASTPredTransMono
  MaybePTMono : ASTPredTransMono MaybePT

  returnPTMono MaybePTMono            x                            P₁ P₂      P₁⊆ₒP₂ unit     wp =
    P₁⊆ₒP₂ _ wp
  bindPTMono   MaybePTMono            f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ nothing  wp .nothing  refl =
    P₁⊆ₒP₂ nothing (wp nothing refl)
  bindPTMono   MaybePTMono            f₁ f₂ mono₁ mono₂ f₁⊑f₂ unit P₁ P₂      P₁⊆ₒP₂ (just x) wp .(just x) refl =
    mono₂ x P₁ P₂ P₁⊆ₒP₂ unit (f₁⊑f₂ x P₁ unit (wp (just x) refl))
  opPTMono     MaybePTMono Maybe-bail f₁ f₂ mono₁ mono₂ f₁⊑f₂      P₁ P₂ unit P₁⊆ₒP₂          wp =
    P₁⊆ₒP₂ nothing wp

  maybePTMono     = predTransMono MaybePTMono
  maybePTMonoBind = bindPTMono    MaybePTMono

  ------------------------------------------------------------------------------
  open ASTSufficientPT
  MaybeSuf : ASTSufficientPT MaybeOpSem MaybePT
  returnSuf MaybeSuf x P i wp = wp
  bindSuf   MaybeSuf {A} {B} m f mSuf fSuf P unit wp
    with runMaybeBase m unit | inspect (runMaybeBase m) unit
  ... |  nothing             | [ eq ] = mSuf _ unit wp nothing (sym eq)
  ... |  just y              | [ eq ] = let wp' = mSuf _ unit wp (just y) (sym eq)
                                         in fSuf y P unit wp'
  opSuf     MaybeSuf Maybe-bail f fSuf P i wp = wp

  ------------------------------------------------------------------------------

  open ASTPredTrans   MaybePT
  open ASTOpSem MaybeOpSem
  open ASTNecessaryPT
  MaybeNec : ASTNecessaryPT MaybeOpSem MaybePT
  returnNec MaybeNec x P _ = id
  bindNec   MaybeNec {A} {B} m f mNec fNec P unit Pr
    with runAST m unit | inspect (runAST m) unit
  ... | nothing | [ eq ] =     mNec _ unit λ where r refl → subst (MaybebindPost _ P) (sym eq) Pr
  ... | just x  | [ eq ] = let rec = fNec x P unit Pr
                            in mNec _ unit λ where r refl → subst (MaybebindPost _ P) (sym eq) (fNec x P unit Pr)
  opNec     MaybeNec Maybe-bail f fNec P i = id

module MaybeAST where
  open        MaybeBase
  open        MaybeBase using (MaybebindPost)                                        public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open        ConditionalExtensions MaybePT MaybeOpSem MaybePTMono MaybeSuf MaybeNec public

  MaybeAST    = ExtAST

  runMaybeAST = runAST

  -- TODO-3: do versions for Either and RWS; generically?
  maybePTApp
      : ∀ {A} {P₁ P₂ : Post A} (m : MaybeAST A) i
        → predTrans m (λ o → P₁ o → P₂ o) i
        → predTrans m P₁ i
        → predTrans m P₂ i
  maybePTApp {_} {P₁} {P₂} m unit imp pt1 =
     necessary m P₂ unit
       (sufficient m (λ o → P₁ o → P₂ o) unit imp
          (sufficient m P₁ unit pt1))

  module MaybeBindProps {A B : Set} {m : MaybeAST A} {f : A → MaybeAST B}
                        (prog : MaybeAST B)
                        (prog≡ : prog ≡ ASTbind m f) where
    justProp : ∀ x
               → runMaybeAST m unit ≡ just x
               → runMaybeAST prog unit ≡ runMaybeAST (f x) unit
    justProp x runm≡justx rewrite prog≡ | runm≡justx = refl

  -- TODO : generalise, does not need to be specific to Maybe
  bindCont : ∀ {A}{B}{m : MaybeAST A}{f : A → MaybeAST B}
             (prog : MaybeAST B)
           → prog ≡ AST.ASTbind m f
           → (A → MaybeAST B)
  bindCont {m = m} {f} prog refl = f

  maybePTBindLemma : ∀ {A B : Set} {m : MaybeAST A} {f : A → MaybeAST B} {P : Post B}{i : Input}
                     → (prog : MaybeAST B)
                     → prog ≡ ASTbind m f
                     → (      runMaybeAST m i ≡ nothing → P nothing)
                     → (∀ x → runMaybeAST m i ≡ just x  → P (runMaybeAST (f x) i))
                     → predTrans prog P i
  maybePTBindLemma {A} {m = m} {f} {P} {unit} prog refl nothingCase justCase
     with runMaybeAST m unit | inspect (runMaybeAST m) unit
  ... | nothing | [ R ] = necessary m _ unit bindPost
        where
        bindPost : _
        bindPost r refl rewrite R = nothingCase refl
  ... | just x  | [ R ] = necessary prog P unit bindPost
        where
        bindPost : _
        bindPost = subst P (sym (MaybeBindProps.justProp prog refl x R)) (justCase x refl)

  maybeSufficient = ASTSufficientPT.sufficient Suf

  maybeSuffBind
    : ∀ {A B P} {Q : Post A} {i} (m : MaybeAST A) (f : A → MaybeAST B)
      → predTrans (m >>= f) P i
      → (P nothing → Q nothing)
      → (∀ x → predTrans (f x) P unit → Q (just x))
      → Q (runMaybeAST m i)
  maybeSuffBind{P = P}{Q}{i} m f wp n⊆ j⊆ =
    MaybebindPost⊆ (λ x → predTrans (f x)) P Q n⊆ j⊆
      (runMaybeAST m i) (maybeSufficient m _ i wp _ refl)

open MaybeAST public

module MaybeSyntax where
  open import Dijkstra.AST.Core
  open import Dijkstra.AST.Branching
  open ASTExtension
  open MaybeBase

  bail : ∀ {A} → AST (BranchOps MaybeOps) A
  bail =  ASTop (Left Maybe-bail) λ ()

open MaybeSyntax public

module MaybeExample where
  -- Here we show a MaybeAST program in terms of the underlying Cmds, which requires opening
  -- MaybeBase
  module _ where
    open import Dijkstra.AST.Core
    open        MaybeBase

    prog₁ : ∀ {A} → A → MaybeAST A
    prog₁ a =
      ASTbind (ASTop (Left (Maybe-bail {Void})) (λ ()))
              (λ _ → ASTreturn  a)

  -- Now we present an equivalent program using the MaybeSyntax, so we don't need to open MaybeBase,
  -- and prove properties about it.  The same proofs work for prog₁ as for prog₁'.
  prog₁' : ∀ {A} → A → MaybeAST A
  prog₁' a = do
    bail {Void}
    return a

  BailWorks : ∀ {A} -> Post A
  BailWorks o = o ≡ nothing

  bailWorks  : ∀ {A} (a : A) i → predTrans (prog₁' a) BailWorks i
  bailWorks  a unit r refl = refl

  -- "expanded" version for understanding
  bailWorks' : ∀ {A} (a : A) i → predTrans (prog₁' a) BailWorks i
  bailWorks' a unit maybeVoid maybeVoid≡nothing
                             -- MaybebindPost (λ x P i → P (just a)) BailWorks           maybeVoid
    with maybeVoid | maybeVoid≡nothing
  ... | n | n≡nothing        -- MaybebindPost (λ x P i → P (just a)) (λ o → o ≡ nothing) n
    rewrite n≡nothing        -- MaybebindPost (λ x P i → P (just a)) (λ o → o ≡ nothing) nothing
    = refl

  -- an easy example using sufficient
  bailWorksSuf  : ∀ {A : Set} (a : A) i → (runMaybeAST (prog₁' a) i ≡ nothing)
  bailWorksSuf a i =
    sufficient (prog₁' a) BailWorks unit (bailWorks a unit)

  -- alternate version, showing that it's trivial in this case
  bailWorksSuf' : ∀ {A : Set} (a : A) i → (runMaybeAST (prog₁' a) i ≡ nothing)
  bailWorksSuf' a i = refl

