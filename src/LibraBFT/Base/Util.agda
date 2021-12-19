{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Level using (0ℓ)
open import Data.String

-- This module defines utility functions to help working on proofs.

module LibraBFT.Base.Util where

  -- These should obviously not be used in any legitimate proof.  They are just for convenience when
  -- we want to avoid importing a module with open holes while working on something else.

  -- This variant allows a comment to be attached conveniently
  obm-dangerous-magic' : ∀ {ℓ} {A : Set ℓ} → String → A
  obm-dangerous-magic' {ℓ} {A} _ = magic
    where postulate magic : A

  obm-dangerous-magic! : ∀ {ℓ} {A : Set ℓ} → A
  obm-dangerous-magic! {ℓ} {A} = obm-dangerous-magic' ""

