{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.Types  -- temporary for testing
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

{-  This is broken now, not sure if we will still want/need it
  LBFT-ec : EpochConfig → Set → Set₁
  LBFT-ec ec = RWST Unit Output (WithEpochConfig.RoundManagerMetaWithEC ec)

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ {ec} → LBFT-ec ec A) → LBFT A
  liftEC f = do
    st ← get
    let ec                 = α-EC (_rmEC st , _rmEC-correct st)
        r₁ , stec₁ , outs₁ = RWST-run (f {ec}) unit (_rmMetaWithEC st)
    tell outs₁
    put (record st { _rmWithEC = stec₁ })
    return r₁
-}



-- Lens functionality
--
-- If we make RWST work for different level State types, we will break use and
-- modify because Lens does not support different levels, we define use and
-- modify' here for RoundManager. We are ok as long as we can keep
-- RoundManager in Set. If we ever need to make RoundManager at some higher
-- Level, we will have to consider making Lens level-agnostic. Preliminary
-- exploration by @cwjnkins showed this to be somewhat painful in particular
-- around composition, so we are not pursuing it for now.

  LBFT-get : LBFT RoundManagerEC
  LBFT-get = gets _rmEC

  LBFT-gets : ∀ {A} → (RoundManagerEC → A) → LBFT A
  LBFT-gets f = gets (f ∘ _rmEC)

  LBFT-getWithMeta : LBFT RoundManager
  LBFT-getWithMeta = get

  LBFT-use : ∀ {A}
           → Lens RoundManagerEC A
           → LBFT A
  LBFT-use l = gets ((_^∙ l) ∘ _rmEC)

  LBFT-modifyL : ∀ {A} → (l : Lens RoundManagerEC A) → ⦃ goodLens : RMLens l ⦄ → (A → A) → LBFT Unit
  LBFT-modifyL l ⦃ gl ⦄ f = modify λ rm → proj₁ (RMLens.getRM gl rm f)
  syntax LBFT-modifyL l f = l LBFT-%= f

  LBFT-setL : ∀ {A} → (l : Lens RoundManagerEC A) → ⦃ goodLens : RMLens l ⦄ → A → LBFT Unit
  LBFT-setL l x = l LBFT-%= const x
  syntax LBFT-setL l x = l LBFT-∙= x

  LBFT-setLMaybe : ∀ {A} → (l : Lens RoundManagerEC (Maybe A)) → ⦃ goodLens : RMLens l ⦄ → A → LBFT Unit
  LBFT-setLMaybe l x = LBFT-setL l (just x)
  syntax LBFT-setLMaybe l x = l LBFT-?= x

  postulate
    st : RoundManager

  testIt1 : Bool → LBFT Unit
  testIt1 b = do
    rmSyncOnly LBFT-∙= b

  _ : (_rmEC (LBFT-post (testIt1 false) st)) ^∙ rmSyncOnly ≡ false
  _ = refl

  testIt2 : LBFT Unit
  testIt2 = do
    rmSyncOnly LBFT-∙= false

  _ : (_rmEC (LBFT-post testIt2 st)) ^∙ rmSyncOnly ≡ false
  _ = refl

  testIt3 : LBFT Bool
  testIt3 = do
    testIt1 false
    x ← LBFT-use rmSyncOnly'  -- Only the primed version works see comment in Types.agda
    return x

  _ : (_rmEC (LBFT-post testIt3 st)) ^∙ rmSyncOnly ≡ false
  _ = refl

  testIt4 : LBFT Bool
  testIt4 = do
    testIt1 false
    x ← LBFT-use rmSyncOnly'
    testIt1 true
    x' ← LBFT-use rmSyncOnly'
    if x then return false
         else if x'
              then return true
              else return false

  _ : (_rmEC (LBFT-post testIt4 st)) ^∙ rmSyncOnly ≡ true
  _ = refl

  testIt5 : SafetyRules → LBFT Unit
  testIt5 sr = do
    rmSafetyRules' LBFT-∙= sr

  testIt6 : Round → LBFT Unit
  testIt6 rnd = do
    rmSafetyRules' LBFT-%= (_& (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound) ∙~ rnd)

  testIt7 : Round → LBFT Unit
  testIt7 rnd = do
    rmSafetyRules' LBFT-%= (_& (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound) ∙~ rnd)


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
