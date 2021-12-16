{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Haskell.RWS
open import LibraBFT.ImplShared.Util.Dijkstra.RWS
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.Prelude
open import Optics.All

-- This module contains definitions allowing RWS programs to be written using
-- Agda's do-notation, as well as convenient short names for operations
-- (including lens operations).
module LibraBFT.ImplShared.Util.Dijkstra.RWS.Syntax where

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- From this instance declaration, we get _<$>_, pure, and _<*>_ also.
instance
  RWS-Monad : Monad (RWS Ev Wr St)
  Monad.return RWS-Monad = RWS-return
  Monad._>>=_  RWS-Monad = RWS-bind

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

tell1 : Wr → RWS Ev Wr St Unit
tell1 x = tell (x ∷ [])

act = tell1

void : RWS Ev Wr St A → RWS Ev Wr St Unit
void m = do
  _ ← m
  pure unit

-- -- Composition with error monad
ok : A → RWS Ev Wr St (B ⊎ A)
ok = pure ∘ Right

bail : B → RWS Ev Wr St (B ⊎ A)
bail = pure ∘ Left

infixl 4 _∙?∙_
_∙?∙_ : RWS Ev Wr St (Either C A) → (A → RWS Ev Wr St (Either C B)) → RWS Ev Wr St (Either C B)
_∙?∙_ = RWS-ebind

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

infixl 4 _∙^∙_
_∙^∙_ : RWS Ev Wr St (Either B A) → (B → B) → RWS Ev Wr St (Either B A)
m ∙^∙ f = do
  x ← m
  either (bail ∘ f) ok x

RWS-weakestPre-∙^∙Post : (ev : Ev) (e : C → C) → RWS-Post Wr St (C ⊎ A) → RWS-Post Wr St (C ⊎ A)
RWS-weakestPre-∙^∙Post ev e Post =
  RWS-weakestPre-bindPost ev (either (bail ∘ e) ok) Post

-- Lens functionality
--
-- If we make RWS work for different level State types, we will break use and
-- modify because Lens does not support different levels, we define use and
-- modify' here for RoundManager. We are ok as long as we can keep
-- RoundManager in Set. If we ever need to make RoundManager at some higher
-- Level, we will have to consider making Lens level-agnostic. Preliminary
-- exploration by @cwjnkins showed this to be somewhat painful in particular
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
