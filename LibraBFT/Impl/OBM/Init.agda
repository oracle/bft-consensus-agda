{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.ConsensusProvider                as ConsensusProvider
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.Liveness.RoundState              as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ExponentialTimeInterval as ExponentialTimeInterval
import      LibraBFT.Impl.IO.OBM.GenKeyFile                          as GenKeyFile
import      LibraBFT.Impl.OBM.ConfigHardCoded                        as ConfigHardCoded
open import LibraBFT.Impl.OBM.Rust.Duration                          as Duration
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Time
import      LibraBFT.Impl.Types.BlockInfo                            as BlockInfo
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.Prelude

module LibraBFT.Impl.OBM.Init where

------------------------------------------------------------------------------
-- Everything below is specific to Agda.

initialize
  : AuthorName → GenKeyFile.NfLiwsVssVvPe → Instant → ObmNeedFetch → ProposalGenerator
  → Either ErrLog (EpochManager × List Output)
initialize me nfLiwsVssVvPe now obmNeedFetch proposalGenerator = do
  (nc , occp , liws , sk , pe) ← ConsensusProvider.obmInitialData me nfLiwsVssVvPe
  ConsensusProvider.startConsensus
    nc now occp liws sk
    obmNeedFetch proposalGenerator
    (StateComputer∙new BlockInfo.gENESIS_VERSION)
