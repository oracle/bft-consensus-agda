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
  open import LibraBFT.Impl.Util.RWST ℓ-RoundManager public
  ----------------
  -- LBFT Monad --
  ----------------

  -- Global 'LBFT'; works over the whole state.
  LBFT : Set → Set
  LBFT = RWST Unit Output RoundManager

  LBFT-run : ∀ {A} → LBFT A → RoundManager → (A × RoundManager × List Output)
  LBFT-run m = RWST-run m unit

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

  LBFT-ec : EpochConfig → Set → Set
  LBFT-ec ec = RWST Unit Output (RoundManagerWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = rwst λ _ st
    → let ec                 = α-EC (₋rmEC st , ₋rmEC-correct st)
          res , stec' , acts = RWST-run (f ec) unit (₋rmWithEC st)
       in res , record st { ₋rmWithEC = stec' } , acts

  -- Type that captures a proof that a computation in the LBFT monad
  -- satisfies a given contract.
  LBFT-Contract : ∀{A} → LBFT A
                → (RoundManager → Set)
                → (RoundManager → Set)
                → Set
  LBFT-Contract f Pre Post =
    ∀ rm → Pre rm × Post (proj₁ (proj₂ (RWST-run f unit rm)))

  -- Because we made RWST work for different level State types, but broke use
  -- and modify' because Lens does not support different levels, we define use
  -- and modify' here for RoundManager.  This will work as long as we can keep
  -- RoundManager in Set.  If we ever need to make RoundManager at some higher
  -- Level, we will have to consider making Lens level-agnostic.  Preliminary
  -- exploration by @cwjnkins showed this to be somewhat painful in particular
  -- around composition, so we are not pursuing it for now.
  use : ∀ {A} → Lens RoundManager A → LBFT A
  use f = RWST-bind get (RWST-return ∘ (_^∙ f))

  modify' : ∀ {A} → Lens RoundManager A → A → LBFT Unit
  modify' l val = modify λ x → x [ l := val ]

