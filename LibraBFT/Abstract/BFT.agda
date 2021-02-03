{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.BFT where

  -- This is a utility function to make it easy to provide the bft-assumption
  -- for the abstract EpochConfig by by assuming that at most bizF members are byzantine
  -- and that authorsN ≥ suc (3 * bizF) and that a list of Members is a quorum if it
  -- contains at least authorsN ∸ bizF distinct Members.

