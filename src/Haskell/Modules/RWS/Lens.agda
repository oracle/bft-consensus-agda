{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Haskell.Modules.RWS.Lens where

open import Haskell.Modules.RWS
open import Haskell.Prelude
open import Optics.All

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- Lens functionality
--
-- If we make RWS work for different level State types, we will break use and
-- modify because Lens does not support different levels, we define use and
-- modify' here for RoundManager. We are ok as long as we can keep
-- RoundManager in Set. If we ever need to make RoundManager at some higher
-- Level, we will have to consider making Lens level-agnostic. Preliminary
-- exploration by ANONYMOUS showed this to be somewhat painful in particular
-- around composition, so we are not pursuing it for now.
use : Lens St A → RWS Ev Wr St A
use f = gets (_^∙ f)

modifyL : Lens St A → (A → A) → RWS Ev Wr St Unit
modifyL l f = modify (over l f)
syntax modifyL l f = l %= f

setL : Lens St A → A → RWS Ev Wr St Unit
setL l x = l %= const x
syntax setL l x = l ∙= x

setL? : Lens St (Maybe A) → A → RWS Ev Wr St Unit
setL? l x = l ∙= just x
syntax setL? l x = l ?= x
