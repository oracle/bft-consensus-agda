{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}


open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Logging.Logging where

logErr : LBFT Unit
logErr = tell1 (LogErr fakeErr)

logInfo : LBFT Unit
logInfo = tell1 (LogInfo fakeInfo)

-- NOTE: The logging functionality below has been added because, in the future,
-- we may wish to model and reason about errors and logging in more detail.
-- Logging operations change the structure of the program, and proofs about peer
-- operations are sensitive to this structure. Therefore, we add a "skeleton" of
-- logging operations so that future refinements do not break existing proofs.
withErrCtxt : ErrLog → ErrLog
withErrCtxt = id

logEE : ∀ {A} → LBFT A → LBFT A
logEE f = logInfo >> f >>= λ r → logInfo >> pure r

lcheck : ∀ {ℓ} {A : Set ℓ} ⦃ _ : ToBool A ⦄ → A → {- List String → -} Either ErrLog Unit
lcheck b {- t -} = case check (toBool b) [] of λ where
  (Left e)  → Left fakeErr
  (Right r) → Right r
