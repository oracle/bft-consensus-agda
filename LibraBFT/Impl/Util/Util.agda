{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Impl.Consensus.Types

-- This module defines the LBFT monad used by our (fake/simple,
-- for now) "implementation", along with some utility functions
-- to facilitate reasoning about it.

module LibraBFT.Impl.Util.Util where
  open import Optics.All
  open import LibraBFT.Impl.Util.RWST public
  open RWST-do
  ----------------
  -- LBFT Monad --
  ----------------

  -- Global 'LBFT'; works over the whole state.
  LBFT : Set → Set₁
  LBFT = RWST Unit Output RoundManager

  LBFT-run : ∀ {A} → LBFT A → RoundManager → (A × RoundManager × List Output)
  LBFT-run m = RWST-run m unit

  LBFT-result : ∀ {A} → LBFT A → RoundManager → A
  LBFT-result m rm = proj₁ (LBFT-run m rm)

  LBFT-post : ∀ {A} → LBFT A → RoundManager → RoundManager
  LBFT-post m rm = proj₁ (proj₂ (LBFT-run m rm))

  LBFT-outs : ∀ {A} → LBFT A → RoundManager → List Output
  LBFT-outs m rm = proj₂ (proj₂ (LBFT-run m rm))

  -- Local 'LBFT' monad; which operates only over the part of
  -- the state that /depends/ on the ec; not the part
  -- of the state that /defines/ the ec.
  --
  -- This is very convenient to define functions that
  -- do not alter the ec.

  LBFT-ec : EpochConfig → Set → Set₁
  LBFT-ec ec = RWST Unit Output (RoundManagerWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = do
    st ← get
    let ec                 = α-EC (₋rmEC st , ₋rmEC-correct st)
        r₁ , stec₁ , outs₁ = RWST-run (f ec) unit (₋rmWithEC st)
    tell outs₁
    put (record st { ₋rmWithEC = stec₁ })
    return r₁

  LBFT-Contract
    : ∀ {A} → LBFT A
      → ((pre : RoundManager) → Set) → ((x : A) (post : RoundManager) (outs : List Output) → Set)
      → Set
  LBFT-Contract m Pre Post =
    ∀ pre →
      let (r , post , outs) = RWST-run m unit pre in
      Pre pre → Post r post outs
