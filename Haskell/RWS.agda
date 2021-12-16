{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- RWS monad implementation, and functionality for proving properties about
-- programs written using this RWS monad.
-- It includes constructors for branching code, to aid in the verification.

module Haskell.RWS where

open import Haskell.Prelude
------------------------------------------------------------------------------
open import Data.Product using (_×_; _,_)

-- RWS, the AST of computations with state `St` reading from an environment
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
  RWS-either : ∀ {A B C} → Either B C
                → (B → RWS Ev Wr St A) → (C → RWS Ev Wr St A)    → RWS Ev Wr St A
  RWS-ebind  : ∀ {A B C}
                → RWS Ev Wr St (Either C A)
                → (A → RWS Ev Wr St (Either C B))                → RWS Ev Wr St (Either C B)
  RWS-maybe  : ∀ {A B} → Maybe B
                → (RWS Ev Wr St A) → (B → RWS Ev Wr St A)        → RWS Ev Wr St A

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
runRWS : RWS Ev Wr St A → Ev → St → A × St × List Wr
runRWS (RWS-return x)               ev st = x , st , []
runRWS (RWS-bind m f)               ev st
   with runRWS m ev st
...| x₁ , st₁ , outs₁
   with runRWS (f x₁) ev st₁
...| x₂ , st₂ , outs₂                     = x₂ , st₂ , outs₁ ++ outs₂
runRWS (RWS-gets f)                 ev st = f st , st , []
runRWS (RWS-put st)                 ev _  = unit , st , []
runRWS RWS-ask                      ev st = ev , st , []
runRWS (RWS-tell outs)              ev st = unit , st , outs
runRWS (RWS-if (clause (b ≔ c) gs)) ev st =
  if toBool b then runRWS c ev st else runRWS (RWS-if gs) ev st
runRWS (RWS-if (otherwise≔ c))      ev st = runRWS c ev st
runRWS (RWS-either (Left x) f₁ f₂)  ev st = runRWS (f₁ x) ev st
runRWS (RWS-either (Right y) f₁ f₂) ev st = runRWS (f₂ y) ev st
runRWS (RWS-ebind m f)              ev st
   with runRWS m ev st
...| Left c , st₁ , outs₁ = Left c , st₁ , outs₁
...| Right a , st₁ , outs₁
   with runRWS (f a) ev st₁
...| r , st₂ , outs₂                      = r , st₂ , outs₁ ++ outs₂
runRWS (RWS-maybe nothing f₁ f₂)    ev st = runRWS f₁ ev st
runRWS (RWS-maybe (just x) f₁ f₂)   ev st = runRWS (f₂ x) ev st

-- Accessors for the result, poststate, and outputs.
RWS-result : RWS Ev Wr St A → Ev → St → A
RWS-result m ev st = fst (runRWS m ev st)

RWS-post : RWS Ev Wr St A → Ev → St → St
RWS-post m ev st = fst (snd (runRWS m ev st))

RWS-outs : RWS Ev Wr St A → Ev → St → List Wr
RWS-outs m ev st = snd (snd (runRWS m ev st))
