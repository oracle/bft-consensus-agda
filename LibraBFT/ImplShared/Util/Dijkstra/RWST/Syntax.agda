{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Util.Dijkstra.RWST
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.Prelude
open import Optics.All

-- This module contains definitions allowing RWST programs to be written using
-- Agda's do-notation, as well as convenient short names for operations
-- (including lens operations).
module LibraBFT.ImplShared.Util.Dijkstra.RWST.Syntax where

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- From this instance declaration, we get _<$>_, pure, and _<*>_ also.
instance
  RWST-Monad : Monad (RWST Ev Wr St)
  Monad.return RWST-Monad = RWST-return
  Monad._>>=_ RWST-Monad = RWST-bind

-- These instance declarations give us variant conditional operations that we
-- can define to play nice with `RWST-weakestPre`

instance
  RWST-MonadIfD : MonadIfD{ℓ₃ = ℓ0} (RWST Ev Wr St)
  MonadIfD.monad RWST-MonadIfD = RWST-Monad
  MonadIfD.ifD‖ RWST-MonadIfD = RWST-if

  RWST-MonadMaybeD : MonadMaybeD (RWST Ev Wr St)
  MonadMaybeD.monad   RWST-MonadMaybeD = RWST-Monad
  MonadMaybeD.maybeSD RWST-MonadMaybeD = RWST-maybe

  RWST-MonadEitherD : MonadEitherD (RWST Ev Wr St)
  MonadEitherD.monad    RWST-MonadEitherD = RWST-Monad
  MonadEitherD.eitherSD RWST-MonadEitherD = RWST-either

gets : (St → A) → RWST Ev Wr St A
gets = RWST-gets

get : RWST Ev Wr St St
get = gets id

put : St → RWST Ev Wr St Unit
put = RWST-put

modify : (St → St) → RWST Ev Wr St Unit
modify f = do
  st ← get
  put (f st)

ask : RWST Ev Wr St Ev
ask = RWST-ask

tell : List Wr → RWST Ev Wr St Unit
tell = RWST-tell

tell1 : Wr → RWST Ev Wr St Unit
tell1 x = tell (x ∷ [])

act = tell1

void : RWST Ev Wr St A → RWST Ev Wr St Unit
void m = do
  _ ← m
  pure unit

-- -- Composition with error monad
ok : A → RWST Ev Wr St (B ⊎ A)
ok = pure ∘ Right

bail : B → RWST Ev Wr St (B ⊎ A)
bail = pure ∘ Left

infixl 4 _∙?∙_
_∙?∙_ : RWST Ev Wr St (Either C A) → (A → RWST Ev Wr St (Either C B)) → RWST Ev Wr St (Either C B)
_∙?∙_ = RWST-ebind

maybeSM : RWST Ev Wr St (Maybe A) → RWST Ev Wr St B → (A → RWST Ev Wr St B) → RWST Ev Wr St B
maybeSM mma mb f = do
  x ← mma
  caseMD x of λ where
    nothing  → mb
    (just j) → f j

maybeSMP-RWST : RWST Ev Wr St (Maybe A) → B → (A → RWST Ev Wr St B)
              → RWST Ev Wr St B
maybeSMP-RWST ma b f = do
  x ← ma
  caseMD x of λ where
    nothing  → pure b
    (just j) → f j

infixl 4 _∙^∙_
_∙^∙_ : RWST Ev Wr St (Either B A) → (B → B) → RWST Ev Wr St (Either B A)
m ∙^∙ f = do
  x ← m
  either (bail ∘ f) ok x

RWST-weakestPre-∙^∙Post : (ev : Ev) (e : C → C) → RWST-Post Wr St (C ⊎ A) → RWST-Post Wr St (C ⊎ A)
RWST-weakestPre-∙^∙Post ev e Post =
  RWST-weakestPre-bindPost ev (either (bail ∘ e) ok) Post

-- Lens functionality
--
-- If we make RWST work for different level State types, we will break use and
-- modify because Lens does not support different levels, we define use and
-- modify' here for RoundManager. We are ok as long as we can keep
-- RoundManager in Set. If we ever need to make RoundManager at some higher
-- Level, we will have to consider making Lens level-agnostic. Preliminary
-- exploration by @cwjnkins showed this to be somewhat painful in particular
-- around composition, so we are not pursuing it for now.
use : Lens St A → RWST Ev Wr St A
use f = gets (_^∙ f)

modifyL : Lens St A → (A → A) → RWST Ev Wr St Unit
modifyL l f = modify (over l f)
syntax modifyL l f = l %= f

setL : Lens St A → A → RWST Ev Wr St Unit
setL l x = l %= const x
syntax setL l x = l ∙= x

setL? : Lens St (Maybe A) → A → RWST Ev Wr St Unit
setL? l x = l ∙= just x
syntax setL? l x = l ?= x