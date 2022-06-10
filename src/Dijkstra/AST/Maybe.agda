{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Maybe where

open import Haskell.Prelude using (_>>_; _>>=_; const; just; Maybe; nothing; return; Unit; unit; Monad; Void; false; true)
open import Data.Product using (Σ; _,_)
import      Level
open import Relation.Binary.PropositionalEquality
open import Util.Prelude using (contradiction; id; Left; Right)

module MaybeBase where

  open import Dijkstra.AST.Core

  data MaybeCmd (C : Set) : Set₁ where
    Maybe-bail : MaybeCmd C

  MaybeSubArg : {C : Set} (c : MaybeCmd C) → Set₁
  MaybeSubArg Maybe-bail = Level.Lift _ Void

  MaybeSubRet : {A : Set} {c : MaybeCmd A} (r : MaybeSubArg c) → Set
  MaybeSubRet {c = Maybe-bail} ()

  MaybeOps : ASTOps
  ASTOps.Cmd    MaybeOps = MaybeCmd
  ASTOps.SubArg MaybeOps = MaybeSubArg
  ASTOps.SubRet MaybeOps = MaybeSubRet

  MaybeBaseAST = AST MaybeOps

  MaybeTypes : ASTTypes
  ASTTypes.Input  MaybeTypes   = Unit
  ASTTypes.Output MaybeTypes A = Maybe A

  open ASTTypes MaybeTypes

  MaybeOpSem : ASTOpSem MaybeOps MaybeTypes
  ASTOpSem.runAST MaybeOpSem (ASTreturn x) _ = just x
  ASTOpSem.runAST MaybeOpSem (ASTbind m f) i
    with ASTOpSem.runAST MaybeOpSem m i
  ...| nothing = nothing
  ...| just x  = ASTOpSem.runAST MaybeOpSem (f x) i
  ASTOpSem.runAST MaybeOpSem (ASTop Maybe-bail f) i = nothing

  runMaybeBase = ASTOpSem.runAST MaybeOpSem

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

  MaybePT : ASTPredTrans MaybeOps MaybeTypes
  ASTPredTrans.returnPT MaybePT x P i               = P (just x)
  -- Note that it is important *not* to pattern match the input as 'unit'.  Even though this is the
  -- only constructor for Unit, Agda does not figure out that this case applies to a general Input
  -- (because Input is of type Unit), and therefore does not expand this case when encountering
  -- bindPT.
  ASTPredTrans.bindPT   MaybePT f i Post x          = ∀ r → r ≡ x → MaybebindPost f Post r
  ASTPredTrans.opPT     MaybePT Maybe-bail f Post i = Post nothing
  -- This open is important because, without it, Agda does not know how to interpret bindPT and
  -- therefore does not refine the goal sufficiently to enable the old λ ._ refl trick to get to the
  -- MaybebindPost goal, for example.
  open ASTPredTrans MaybePT

  MaybePTMono : ASTPredTransMono MaybePT
  ASTPredTransMono.returnPTMono MaybePTMono x P₁ P₂ P₁⊆ₒP₂ i wp =
    P₁⊆ₒP₂ _ wp

  ASTPredTransMono.bindPTMono₁  MaybePTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ nothing  wp .nothing  refl =
    P₁⊆ₒP₂ nothing (wp nothing refl)
  ASTPredTransMono.bindPTMono₁  MaybePTMono f monoF unit P₁ P₂ P₁⊆ₒP₂ (just y) wp .(just y) refl =
    monoF y P₁ P₂ P₁⊆ₒP₂ unit (wp (just y) refl)

  ASTPredTransMono.bindPTMono₂  MaybePTMono {B1} {B2} f₁ f₂ f₁⊑f₂ unit P nothing wp .nothing refl =
    wp nothing refl
  ASTPredTransMono.bindPTMono₂  MaybePTMono f₁ f₂ f₁⊑f₂ unit P (just y) wp .(just y) refl =
    f₁⊑f₂ y _ unit (wp (just y) refl)

  ASTPredTransMono.opPTMono₁    MaybePTMono Maybe-bail f monoF P₁ P₂ P₁⊆ₒP₂ unit wp =
    P₁⊆ₒP₂ nothing wp
  ASTPredTransMono.opPTMono₂    MaybePTMono Maybe-bail f₁ f₂ f₁⊑f₂ P i wp =
    wp

  maybePTMono      = ASTPredTransMono.predTransMono MaybePTMono
  maybePTMonoBind₂ = ASTPredTransMono.bindPTMono₂   MaybePTMono

  MaybeSuf : ASTSufficientPT MaybeOpSem MaybePT
  ASTSufficientPT.returnSuf MaybeSuf x P i wp = wp
  ASTSufficientPT.bindSuf   MaybeSuf {A} {B} m f mSuf fSuf P unit wp
    with runMaybeBase m unit | inspect (runMaybeBase m) unit
  ... |  nothing             | [ eq ] = mSuf _ unit wp nothing (sym eq)
  ... |  just y              | [ eq ] = let wp' = mSuf _ unit wp (just y) (sym eq)
                                         in fSuf y P unit wp'
  ASTSufficientPT.opSuf     MaybeSuf Maybe-bail f fSuf P i wp = wp

module MaybeAST where
  open        MaybeBase
  open        MaybeBase using (MaybebindPost)                               public
  open import Dijkstra.AST.Branching
  open import Dijkstra.AST.Core
  open        ConditionalExtensions MaybePT MaybeOpSem MaybePTMono MaybeSuf public

  MaybeAST    = ExtAST

  runMaybeAST = runAST

  -- This property says that predTrans really is the *weakest* precondition for a
  -- postcondition to hold after running a MaybeAST.
  Post⇒wp : ∀ {A} → MaybeAST A → Input → Set₁
  Post⇒wp {A} m i =
    (P : Post A)
    → P (runMaybeAST m i)
    → predTrans m P i

  predTrans-is-weakest : ∀ {A} → (m : MaybeAST A) → Post⇒wp {A} m unit
  predTrans-is-weakest (ASTreturn _) _ = id
  predTrans-is-weakest (ASTbind m f) _ Pr
     with predTrans-is-weakest m
  ...| rec
    with runMaybeAST m unit
  ... | nothing = rec _ λ where _ refl → Pr
  ... | just x  = rec _ λ where r refl → predTrans-is-weakest (f x) _ Pr
  predTrans-is-weakest (ASTop (Left Maybe-bail) f)    Pr = id
  predTrans-is-weakest (ASTop (Right (BCif b)) f) Pr
     with predTrans-is-weakest (f (Level.lift b))
  ...| rec = λ x → (λ where   refl → rec Pr x) , (λ where   refl → rec Pr x)
  predTrans-is-weakest (ASTop (Right (BCeither b)) f) Pr
     with predTrans-is-weakest (f (Level.lift b))
  ...| rec = λ x → (λ where r refl → rec Pr x) , (λ where r refl → rec Pr x)
  predTrans-is-weakest (ASTop (Right (BCmaybe mb)) f) Pr
     with predTrans-is-weakest (f (Level.lift mb))
  ...| rec = λ x → (λ where   refl → rec Pr x) , (λ where j refl → rec Pr x)

  maybePTApp
      : ∀ {A} {P₁ P₂ : Post A} (m : MaybeAST A) i
        → predTrans m (λ o → P₁ o → P₂ o) i
        → predTrans m P₁ i
        → predTrans m P₂ i
  maybePTApp {_} {P₁} {P₂} m unit imp pt1 =
    predTrans-is-weakest m P₂
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
  ... | nothing | [ R ] = predTrans-is-weakest m _ bindPost
        where
        bindPost : _
        bindPost r refl rewrite R = nothingCase refl
  ... | just x  | [ R ] = predTrans-is-weakest prog P bindPost
        where
        bindPost : _
        bindPost = subst P (sym (MaybeBindProps.justProp prog refl x R)) (justCase x refl)

  maybeSufficient = ASTSufficientPT.sufficient Suf

  -- TODO: make these apply to MaybeExt, use in Partiality
  maybeSuffBind
    : ∀ {A B P} {Q : Post A} {i} (m : MaybeAST A) (f : A → MaybeAST B)
      → predTrans (m >>= f) P i
      → (P nothing → Q nothing)
      → (∀ x → predTrans (f x) P unit → Q (just x))
      → Q (runMaybeAST m i)
  maybeSuffBind{P = P}{Q}{i} m f wp n⊆ j⊆ =
    MaybebindPost⊆ (λ x → predTrans (f x)) P Q n⊆ j⊆
      (runMaybeAST m i) (maybeSufficient m _ i wp _ refl)

module MaybeSyntax where
  open import Dijkstra.AST.Core
  open import Dijkstra.AST.Branching
  open ASTExtension
  open MaybeBase

  bail : ∀ {A} → AST (BranchOps MaybeOps) A
  bail =  ASTop (Left Maybe-bail) λ ()

open MaybeAST     public
open MaybeSyntax  public

module MaybeExample where
  open MaybeAST
  open MaybeSyntax

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

