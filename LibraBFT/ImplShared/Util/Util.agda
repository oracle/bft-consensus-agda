{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output

-- This module defines the LBFT monad used by our (fake/simple,
-- for now) "implementation", along with some utility functions
-- to facilitate reasoning about it.

module LibraBFT.ImplShared.Util.Util where
  open import Optics.All
  open import LibraBFT.ImplShared.Util.RWST        public
  open import LibraBFT.ImplShared.Util.RWST.Syntax public
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
    let ec                 = α-EC (_rmEC st , _rmEC-correct st)
        r₁ , stec₁ , outs₁ = RWST-run (f ec) unit (_rmWithEC st)
    tell outs₁
    put (record st { _rmWithEC = stec₁ })
    return r₁

  LBFT-Pre  = RoundManager → Set
  LBFT-Post = RWST-Post Output RoundManager

  LBFT-weakestPre : ∀ {A} (m : LBFT A)
                    → LBFT-Post A → LBFT-Pre
  LBFT-weakestPre m Post pre = RWST-weakestPre m Post unit pre

  LBFT-Contract : ∀ {A} (m : LBFT A) → Set₁
  LBFT-Contract{A} m =
    (Post : RWST-Post Output RoundManager A)
    → (pre : RoundManager) → LBFT-weakestPre m Post pre
    → let (x , post , outs) = LBFT-run m pre in
      Post x post outs

  LBFT-contract : ∀ {A} (m : LBFT A) → LBFT-Contract m
  LBFT-contract m Post pre pf = RWST-contract m Post unit pre pf

  LBFT-⇒
    : ∀ {A} (P Q : RWST-Post Output RoundManager A) → (∀ r st outs → P r st outs → Q r st outs)
    → ∀ m pre → LBFT-weakestPre m P pre → LBFT-weakestPre m Q pre
  LBFT-⇒ Post₁ Post₂ f m pre pf = RWST-⇒ Post₁ Post₂ f m unit pre pf
