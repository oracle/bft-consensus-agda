{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS                  as PKCS hiding (sign; verify)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Prelude where

-- Stops and returns at first 'just'.
-- If not 'just' found, then 'nothing'.
find' : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe B
find' _      []  = nothing
find' f (x ∷ xs) = case f x of λ where
  (just b) → just b
  nothing  → find' f xs
