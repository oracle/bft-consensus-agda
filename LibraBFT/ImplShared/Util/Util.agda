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
  open import LibraBFT.ImplShared.Util.Dijkstra.Syntax public
  open import LibraBFT.ImplShared.Util.Dijkstra.RWST public
  open import LibraBFT.ImplShared.Util.Dijkstra.RWST.Syntax public
  open import LibraBFT.ImplShared.Util.Dijkstra.EitherD public
  open import LibraBFT.ImplShared.Util.Dijkstra.EitherD.Syntax public
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

  LBFT-Pre  = RoundManager → Set
  LBFT-Post = RWST-Post Output RoundManager

  LBFT-Post-True : ∀ {A} → LBFT-Post A → LBFT A → RoundManager → Set
  LBFT-Post-True Post m pre =
    let (x , post , outs) = LBFT-run m pre in
    Post x post outs

  LBFT-weakestPre : ∀ {A} (m : LBFT A)
                    → LBFT-Post A → LBFT-Pre
  LBFT-weakestPre m Post pre = RWST-weakestPre m Post unit pre

  LBFT-Contract : ∀ {A} (m : LBFT A) → Set₁
  LBFT-Contract{A} m =
    (Post : RWST-Post Output RoundManager A)
    → (pre : RoundManager) → LBFT-weakestPre m Post pre
    → LBFT-Post-True Post m pre

  LBFT-contract : ∀ {A} (m : LBFT A) → LBFT-Contract m
  LBFT-contract m Post pre pf = RWST-contract m Post unit pre pf

  LBFT-⇒
    : ∀ {A} (P Q : LBFT-Post A) → (RWST-Post-⇒ P Q)
    → ∀ m pre → LBFT-weakestPre m P pre → LBFT-weakestPre m Q pre
  LBFT-⇒ Post₁ Post₂ f m pre pf = RWST-⇒ Post₁ Post₂ f m unit pre pf

  LBFT-⇒-bind
    : ∀ {A B} (P : LBFT-Post A) (Q : LBFT-Post B) (f : A → LBFT B)
      → (RWST-Post-⇒ P (RWST-weakestPre-bindPost unit f Q))
      → ∀ m st → LBFT-weakestPre m P st → LBFT-weakestPre (m >>= f) Q st
  LBFT-⇒-bind Post Q f pf m st con = RWST-⇒-bind Post Q f unit pf m st con

  LBFT-⇒-ebind
    : ∀ {A B C} (P : LBFT-Post (Either C A)) (Q : LBFT-Post (Either C B))
      → (f : A → LBFT (Either C B))
      → RWST-Post-⇒ P (RWST-weakestPre-ebindPost unit f Q)
      → ∀ m st → LBFT-weakestPre m P st
      → LBFT-weakestPre (m ∙?∙ f) Q st
  LBFT-⇒-ebind Post Q f pf m st con =
    RWST-⇒-ebind Post Q f unit pf m st con
