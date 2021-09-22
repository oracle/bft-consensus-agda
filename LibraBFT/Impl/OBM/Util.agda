{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Util where

-- To tolerate f failures, cluster must contain at least n ≥ 3f + 1 nodes,
-- where n − f nodes form a quorum, assuming 1 vote per node.
-- Note: our Haskell implementation and our model of it support non-uniform voting power,
-- that is NOT reflected in these functions, but is reflected in functions in ValidatorVerifier.

numNodesNeededForNFailures : U64 -> U64
numNodesNeededForNFailures numFaultsAllowed = 3 * numFaultsAllowed + 1

checkBftAndRun : ∀ {names : Set} {b : Set}
               → U64 → List names → (U64 → List names → b)
               → Either ErrLog b
checkBftAndRun numFailures authors f =
  if-dec length authors <? numNodesNeededForNFailures numFailures
  then Left fakeErr --(ErrL [ "checkBftAndRun: not enough authors for given number of failures"
                    --      , show numFailures, show (length authors) ])
  else pure (f numFailures authors)
