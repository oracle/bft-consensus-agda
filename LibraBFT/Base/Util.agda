{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Level using (0ℓ)

-- This module defines utility functions to help working on proofs.

module LibraBFT.Base.Util where

  -- This is obviously not something that should be used in any legitimate proof.  It's just for
  -- convenience when we want to avoid importing a module with open holes while working on
  -- something else.
  obm-dangerous-magic! : ∀ {ℓ} {A : Set ℓ} → A
  obm-dangerous-magic! {ℓ} {A} = magic
    where postulate magic : A
