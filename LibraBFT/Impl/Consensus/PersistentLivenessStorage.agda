{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.PersistentLivenessStorage where

postulate
  saveTreeE : ∀ {𝓔 : EpochConfig}
            → BlockStore 𝓔 → List Block → List QuorumCert
            → Either ErrLog (BlockStore 𝓔)
  saveVoteM : Vote → LBFT (Either ErrLog Unit)
