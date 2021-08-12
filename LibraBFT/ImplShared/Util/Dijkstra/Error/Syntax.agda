{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Util.Dijkstra.Error
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.Prelude

module LibraBFT.ImplShared.Util.Dijkstra.Error.Syntax where

private
  variable
    E     : Set
    A B C : Set

-- From this instance declaration, we get _<$>_, pure, and _<*>_ also.
instance
  Monad-Error : ∀ {E : Set} → Monad (Error E)
  Monad.return Monad-Error = Error-return
  Monad._>>=_  Monad-Error = Error-bind

-- These instance declarations give us variant conditional operations that we
-- can define to play nice with `Error-weakestPre`

instance
  Error-MonadIfD : MonadIfD{ℓ₃ = ℓ0} (Error E)
  MonadIfD.monad Error-MonadIfD = Monad-Error
  MonadIfD.ifD‖  Error-MonadIfD = Error-if

  Error-MonadMaybeD : MonadMaybeD (Error E)
  MonadMaybeD.monad   Error-MonadMaybeD = Monad-Error
  MonadMaybeD.maybeSD Error-MonadMaybeD = Error-maybe
