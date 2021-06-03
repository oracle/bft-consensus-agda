{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Impl.Consensus.Types

-- This module defines the Dijkstra-LBFT monad used by our (fake/simple, for
-- now) "implementation", along with some utility functions to facilitate
-- reasoning about it.

module LibraBFT.Impl.Util.D-LBFT where
open import Optics.All
open import LibraBFT.Impl.Util.D-RWST public

----------------
-- LBFT Monad --
----------------

-- Global 'LBFT'; works over the whole state.
D-LBFT : Set → Set₂
D-LBFT = D-RWST Unit Output RoundManager

D-LBFT-run : ∀ {A} → D-LBFT A → RoundManager → (A × RoundManager × List Output)
D-LBFT-run m = D-RWST-run m unit

D-LBFT-result : ∀ {A} → D-LBFT A → RoundManager → A
D-LBFT-result m rm = proj₁ (D-LBFT-run m rm)

D-LBFT-post : ∀ {A} → D-LBFT A → RoundManager → RoundManager
D-LBFT-post m rm = proj₁ (proj₂ (D-LBFT-run m rm))

D-LBFT-outs : ∀ {A} → D-LBFT A → RoundManager → List Output
D-LBFT-outs m rm = proj₂ (proj₂ (D-LBFT-run m rm))

-- Local 'LBFT' monad; which operates only over the part of
-- the state that /depends/ on the ec; not the part
-- of the state that /defines/ the ec.
--
-- This is very convenient to define functions that
-- do not alter the ec.

D-LBFT-ec : EpochConfig → Set → Set₂
D-LBFT-ec ec = D-RWST Unit Output (RoundManagerWithEC ec)

