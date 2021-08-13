{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.Prelude

module LibraBFT.ImplShared.Util.Dijkstra.EitherD.Syntax where

private
  variable
    E     : Set
    A B C : Set

-- From this instance declaration, we get _<$>_, pure, and _<*>_ also.
instance
  Monad-EitherD : ∀ {E : Set} → Monad (EitherD E)
  Monad.return Monad-EitherD = EitherD-return
  Monad._>>=_  Monad-EitherD = EitherD-bind

-- These instance declarations give us variant conditional operations that we
-- can define to play nice with `EitherD-weakestPre`

instance
  EitherD-MonadIfD : MonadIfD{ℓ₃ = ℓ0} (EitherD E)
  MonadIfD.monad EitherD-MonadIfD = Monad-EitherD
  MonadIfD.ifD‖  EitherD-MonadIfD = EitherD-if

  EitherD-MonadMaybeD : MonadMaybeD (EitherD E)
  MonadMaybeD.monad   EitherD-MonadMaybeD = Monad-EitherD
  MonadMaybeD.maybeSD EitherD-MonadMaybeD = EitherD-maybe

  EitherD-MonadEitherD : MonadEitherD (EitherD E)
  MonadEitherD.monad    EitherD-MonadEitherD = Monad-EitherD
  MonadEitherD.eitherSD EitherD-MonadEitherD = EitherD-either

-- `EitherD` is Either-like
instance
  EitherD-EitherLike : EitherLike EitherD
  EitherLike.fromEither EitherD-EitherLike (Left  a) = EitherD-bail a
  EitherLike.fromEither EitherD-EitherLike (Right b) = EitherD-return b

  EitherLike.toEither   EitherD-EitherLike = EitherD-run
