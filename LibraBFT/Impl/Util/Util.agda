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
  open import LibraBFT.Impl.Util.RWST 1ℓ public
  import      LibraBFT.Impl.Util.RWST 0ℓ as ℓ0-RWST
  ----------------
  -- LBFT Monad --
  ----------------

  -- Global 'LBFT'; works over the whole state.
  LBFT : Set → Set ℓ-EventProcessorAndMeta
  LBFT = RWST Unit Output EventProcessorAndMeta

  LBFT-run : ∀ {A} → LBFT A → EventProcessorAndMeta → (A × EventProcessorAndMeta × List Output)
  LBFT-run m = RWST-run m unit

  LBFT-post : ∀ {A} → LBFT A → EventProcessorAndMeta → EventProcessorAndMeta
  LBFT-post m ep = proj₁ (proj₂ (LBFT-run m ep))

  LBFT-outs : ∀ {A} → LBFT A → EventProcessorAndMeta → List Output
  LBFT-outs m ep = proj₂ (proj₂ (LBFT-run m ep))

  -- Local 'LBFT' monad; which operates only over the part of
  -- the state that /depends/ on the ec; not the part
  -- of the state that /defines/ the ec.
  --
  -- This is very convenient to define functions that
  -- do not alter the ec.

  LBFT-ec : EpochConfig → Set → Set
  LBFT-ec ec = ℓ0-RWST.RWST Unit Output (EventProcessorWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = rwst λ _ (mkEventProcessorAndMeta st n𝓔 𝓔s)
    → let ec                 = α-EC (₋epEC st , ₋epEC-correct st)
          res , stec' , acts = ℓ0-RWST.RWST-run (f ec) unit (₋epWithEC st)
       in res , mkEventProcessorAndMeta (record st { ₋epWithEC = stec' }) n𝓔 𝓔s , acts

  -- Type that captures a proof that a computation in the LBFT monad
  -- satisfies a given contract.
  LBFT-Contract : ∀{A} → LBFT A
                → (EventProcessorAndMeta → Set)
                → (EventProcessorAndMeta → Set)
                → Set ℓ-EventProcessorAndMeta
  LBFT-Contract f Pre Post =
    ∀ ep → Pre ep × Post (proj₁ (proj₂ (RWST-run f unit ep)))
