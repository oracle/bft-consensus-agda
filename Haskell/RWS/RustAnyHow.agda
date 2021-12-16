{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.RWS.RustAnyHow where

open import Haskell.Prelude
open import Haskell.RWS

private
  variable
    Ev Wr St : Set
    A B C    : Set

ok   : A → RWS Ev Wr St (Either B A)
ok   = pure ∘ Right

bail : B → RWS Ev Wr St (Either B A)
bail = pure ∘ Left

infixl 4 _∙?∙_
_∙?∙_ : RWS Ev Wr St (Either C A) → (A → RWS Ev Wr St (Either C B)) → RWS Ev Wr St (Either C B)
_∙?∙_ = RWS-ebind

infixl 4 _∙^∙_
_∙^∙_ : RWS Ev Wr St (Either B A) → (B → B) → RWS Ev Wr St (Either B A)
m ∙^∙ f = do
  x ← m
  either (bail ∘ f) ok x


