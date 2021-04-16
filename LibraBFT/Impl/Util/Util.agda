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
  LBFT : Set → Set ℓ-RoundManagerAndMeta
  LBFT = RWST Unit Output RoundManagerAndMeta

  LBFT-run : ∀ {A} → LBFT A → RoundManagerAndMeta → (A × RoundManagerAndMeta × List Output)
  LBFT-run m = RWST-run m unit

  LBFT-post : ∀ {A} → LBFT A → RoundManagerAndMeta → RoundManagerAndMeta
  LBFT-post m rm = proj₁ (proj₂ (LBFT-run m rm))

  LBFT-outs : ∀ {A} → LBFT A → RoundManagerAndMeta → List Output
  LBFT-outs m rm = proj₂ (proj₂ (LBFT-run m rm))

  -- Local 'LBFT' monad; which operates only over the part of
  -- the state that /depends/ on the ec; not the part
  -- of the state that /defines/ the ec.
  --
  -- This is very convenient to define functions that
  -- do not alter the ec.

  LBFT-ec : EpochConfig → Set → Set
  LBFT-ec ec = ℓ0-RWST.RWST Unit Output (RoundManagerWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = rwst λ _ (mkRoundManagerAndMeta st n𝓔 𝓔s)
    → let ec                 = α-EC (₋rmEC st , ₋rmEC-correct st)
          res , stec' , acts = ℓ0-RWST.RWST-run (f ec) unit (₋rmWithEC st)
       in res , mkRoundManagerAndMeta (record st { ₋rmWithEC = stec' }) n𝓔 𝓔s , acts

  -- Type that captures a proof that a computation in the LBFT monad
  -- satisfies a given contract.
  LBFT-Contract : ∀{A} → LBFT A
                → (RoundManagerAndMeta → Set)
                → (RoundManagerAndMeta → Set)
                → Set ℓ-RoundManagerAndMeta
  LBFT-Contract f Pre Post =
    ∀ rm → Pre rm × Post (proj₁ (proj₂ (RWST-run f unit rm)))
