{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions allowing RWS programs to be written using
-- Agda's do-notation, as well as convenient short names for operations
-- (including lens operations).
module Dijkstra.RWS.Syntax where

open import Dijkstra.RWS
open import Dijkstra.Syntax
open import Haskell.Modules.RWS public
open import Haskell.Modules.RWS.Lens public
open import Haskell.Modules.RWS.RustAnyHow public
open import Haskell.Prelude

open import Level
  renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
  public

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- These instance declarations give us variant conditional operations that we
-- can define to play nice with `RWS-weakestPre`

instance
  RWS-MonadIfD : MonadIfD{ℓ₃ = ℓ0} (RWS Ev Wr St)
  MonadIfD.monad RWS-MonadIfD = RWS-Monad
  MonadIfD.ifD‖  RWS-MonadIfD = RWS-if

  RWS-MonadMaybeD : MonadMaybeD (RWS Ev Wr St)
  MonadMaybeD.monad   RWS-MonadMaybeD = RWS-Monad
  MonadMaybeD.maybeSD RWS-MonadMaybeD = RWS-maybe

  RWS-MonadEitherD : MonadEitherD (RWS Ev Wr St)
  MonadEitherD.monad    RWS-MonadEitherD = RWS-Monad
  MonadEitherD.eitherSD RWS-MonadEitherD = RWS-either

maybeSM : RWS Ev Wr St (Maybe A) → RWS Ev Wr St B → (A → RWS Ev Wr St B) → RWS Ev Wr St B
maybeSM mma mb f = do
  x ← mma
  caseMD x of λ where
    nothing  → mb
    (just j) → f j

maybeSMP-RWS : RWS Ev Wr St (Maybe A) → B → (A → RWS Ev Wr St B)
              → RWS Ev Wr St B
maybeSMP-RWS ma b f = do
  x ← ma
  caseMD x of λ where
    nothing  → pure b
    (just j) → f j

RWS-weakestPre-∙^∙Post : (ev : Ev) (e : C → C) → RWS-Post Wr St (Either C A) → RWS-Post Wr St (Either C A)
RWS-weakestPre-∙^∙Post ev e Post =
  RWS-weakestPre-bindPost ev (either (bail ∘ e) ok) Post

