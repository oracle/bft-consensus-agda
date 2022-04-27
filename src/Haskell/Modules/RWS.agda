{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- RWS monad implementation, and functionality for proving properties about
-- programs written using this RWS monad.
-- It includes constructors for branching code, to aid in the verification.

module Haskell.Modules.RWS where

open import Haskell.Prelude
------------------------------------------------------------------------------
open import Data.Product using (_×_; _,_)

-- (free) RWS : the AST of computations with state `St` reading from an environment
-- `Ev` and producing a list of outputs of type `Wr`
data RWS (Ev Wr St : Set) : Set → Set₁ where
  -- Primitive combinators
  RWS-return : ∀ {A}   → A                                       → RWS Ev Wr St A
  RWS-bind   : ∀ {A B} → RWS Ev Wr St A → (A → RWS Ev Wr St B)   → RWS Ev Wr St B
  RWS-gets   : ∀ {A} → (St → A)                                  → RWS Ev Wr St A
  RWS-put    : St                                                → RWS Ev Wr St Unit
  RWS-ask    :                                                     RWS Ev Wr St Ev
  RWS-tell   : List Wr                                           → RWS Ev Wr St Unit
  -- Branching combinators (used for creating more convenient contracts)
  RWS-if     : ∀ {A} → Guards (RWS Ev Wr St A)                   → RWS Ev Wr St A
  RWS-either : ∀ {A B C}
             → (B → RWS Ev Wr St A) → (C → RWS Ev Wr St A)
             → Either B C                                        → RWS Ev Wr St A
  RWS-ebind  : ∀ {A B C}
             → RWS Ev Wr St (Either C A)
             → (A → RWS Ev Wr St (Either C B))                   → RWS Ev Wr St (Either C B)
  RWS-maybe  : ∀ {A B}
             → (RWS Ev Wr St A) → (B → RWS Ev Wr St A) → Maybe B → RWS Ev Wr St A

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- From this instance declaration, we get _<$>_, pure, and _<*>_ also.
instance
  RWS-Monad : Monad (RWS Ev Wr St)
  Monad.return RWS-Monad = RWS-return
  Monad._>>=_  RWS-Monad = RWS-bind

gets : (St → A) → RWS Ev Wr St A
gets = RWS-gets

get : RWS Ev Wr St St
get = gets id

put : St → RWS Ev Wr St Unit
put = RWS-put

modify : (St → St) → RWS Ev Wr St Unit
modify f = do
  st ← get
  put (f st)

ask : RWS Ev Wr St Ev
ask = RWS-ask

tell : List Wr → RWS Ev Wr St Unit
tell = RWS-tell

void : RWS Ev Wr St A → RWS Ev Wr St Unit
void m = do
  _ ← m
  pure unit

-- To execute an RWS program, you provide an environment and prestate.
-- This produces a result value, poststate, and list of outputs.
RWS-run : RWS Ev Wr St A → Ev → St → A × St × List Wr
RWS-run (RWS-return x)               ev st = x , st , []
RWS-run (RWS-bind m f)               ev st
   with RWS-run m ev st
...| x₁ , st₁ , outs₁
   with RWS-run (f x₁) ev st₁
...| x₂ , st₂ , outs₂                      = x₂ , st₂ , outs₁ ++ outs₂
RWS-run (RWS-gets f)                 ev st = f st , st , []
RWS-run (RWS-put st)                 ev _  = unit , st , []
RWS-run RWS-ask                      ev st = ev , st , []
RWS-run (RWS-tell outs)              ev st = unit , st , outs
RWS-run (RWS-if (clause (b ≔ c) gs)) ev st =
  if toBool b then RWS-run c ev st else RWS-run (RWS-if gs) ev st
RWS-run (RWS-if (otherwise≔ c))      ev st = RWS-run c ev st
RWS-run (RWS-either f₁ f₂ (Left x) ) ev st = RWS-run (f₁ x) ev st
RWS-run (RWS-either f₁ f₂ (Right y)) ev st = RWS-run (f₂ y) ev st
RWS-run (RWS-ebind m f)              ev st
   with RWS-run m ev st
...| Left  c , st₁ , outs₁ = Left c , st₁ , outs₁
...| Right a , st₁ , outs₁
   with RWS-run (f a) ev st₁
...|       r , st₂ , outs₂                 = r , st₂ , outs₁ ++ outs₂
RWS-run (RWS-maybe f₁ f₂ nothing )   ev st = RWS-run f₁ ev st
RWS-run (RWS-maybe f₁ f₂ (just x))   ev st = RWS-run (f₂ x) ev st

-- Accessors for the result, poststate, and outputs.
RWS-result : RWS Ev Wr St A → Ev → St → A
RWS-result m ev st =      fst (RWS-run m ev st)

RWS-post   : RWS Ev Wr St A → Ev → St → St
RWS-post   m ev st = fst (snd (RWS-run m ev st))

RWS-outs   : RWS Ev Wr St A → Ev → St → List Wr
RWS-outs   m ev st = snd (snd (RWS-run m ev st))
