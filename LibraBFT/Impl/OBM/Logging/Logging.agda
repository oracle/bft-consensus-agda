{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Haskell.RWS
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import LibraBFT.Prelude
------------------------------------------------------------------------------
open import Data.String                          using (String)

module LibraBFT.Impl.OBM.Logging.Logging where

-- NOTE: Logging operations change the structure of the program, and proofs about peer
-- operations are sensitive to this structure. Therefore, we add a "skeleton" of
-- logging operations so that future refinements do not break existing proofs.
-- In the future, we may wish to model and reason about errors and logging in more detail.

postulate -- TODO-1 : errText : Note, the existing Agda ErrLog constructors do not contain text.
  errText  : ErrLog → List String
  errText' : ErrLog →      String

logErr  : ErrLog → LBFT Unit
logErr  x = tell (LogErr  x ∷ [])

logInfo : InfoLog → LBFT Unit
logInfo x = tell (LogInfo x ∷ [])

logEE : ∀ {A} → List String → LBFT A → LBFT A
logEE _ f = logInfo fakeInfo >> f >>= λ r → logInfo fakeInfo >> pure r

withErrCtx : List String → ErrLog → ErrLog
withErrCtx _ = id

withErrCtx' : ∀ {A} → List String → Either ErrLog A → Either ErrLog A
withErrCtx' ctx = λ where
  (Left  e) → Left (withErrCtx ctx e)
  (Right b) → pure b

withErrCtxD'
  : ∀ {ℓ} {E : Set → Set → Set ℓ} ⦃ _ : EitherLike E ⦄
  → ∀ {A : Set} → List String → E ErrLog A → EitherD ErrLog A
withErrCtxD' ctx e = case toEither e of λ where
  (Left  e) → fromEither $ Left (withErrCtx ctx e)
  (Right b) → fromEither $ Right b

lcheck : ∀ {ℓ} {B : Set ℓ} ⦃ _ : ToBool B ⦄ → B → List String → Either ErrLog Unit
lcheck b t = case check (toBool b) t of λ where
  (Left  e) → Left  fakeErr -- (ErrL [e])
  (Right r) → Right r

lcheckInfo : ∀ {ℓ} {B : Set ℓ} ⦃ _ : ToBool B ⦄ → B → List String → Either ErrLog Unit

lcheckInfo b t = case check (toBool b) t of λ where
  (Left  _) → Left (ErrInfo fakeInfo {-InfoL [e]-})
  (Right r) → Right r
