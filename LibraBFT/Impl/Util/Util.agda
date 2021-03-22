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
  open import LibraBFT.Impl.Util.RWST public
  ----------------
  -- LBFT Monad --
  ----------------

  -- Global 'LBFT'; works over the whole state.
  LBFT : Set → Set
  LBFT = RWST Unit Output EventProcessor

  LBFT-run : ∀ {A} → LBFT A → EventProcessor → (A × EventProcessor × List Output)
  LBFT-run m = RWST-run m unit

  LBFT-outs : ∀ {A} → LBFT A → EventProcessor → List Output
  LBFT-outs m ep = proj₂ (proj₂ (LBFT-run m ep))

  -- Local 'LBFT' monad; which operates only over the part of
  -- the state that /depends/ on the ec; not the part
  -- of the state that /defines/ the ec.
  --
  -- This is very convenient to define functions that
  -- do not alter the ec.

  LBFT-ec : EpochConfig → Set → Set
  LBFT-ec ec = RWST Unit Output (EventProcessorWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = rwst λ _ st
    → let ec                 = α-EC (₋epEC st , ₋epEC-correct st)
          res , stec' , acts = RWST-run (f ec) unit (₋epWithEC st)
       in res , record st { ₋epWithEC = stec' } , acts

  -- Type that captures a proof that a computation in the LBFT monad
  -- satisfies a given contract.
  LBFT-Contract : ∀{A} → LBFT A
                → (EventProcessor → Set)
                → (EventProcessor → Set)
                → Set
  LBFT-Contract f Pre Post =
    ∀ ep → Pre ep × Post (proj₁ (proj₂ (RWST-run f unit ep)))
