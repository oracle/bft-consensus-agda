{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusProvider      as ConsensusProvider
open import LibraBFT.Impl.Properties.Util
import      LibraBFT.Impl.IO.OBM.GenKeyFile                as GenKeyFile
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.ValidatorVerifier          as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.PKCS
open import Util.Prelude                                   hiding (_++_)

module LibraBFT.Impl.Consensus.Properties.ConsensusProvider where

open InitProofDefs

module startConsensusSpec
  (nodeConfig : NodeConfig)
  (now        : Instant)
  (payload    : OnChainConfigPayload)
  (liws       : LedgerInfoWithSignatures)
  (sk         : SK)
  (needFetch  : ObmNeedFetch)
  (propGen    : ProposalGenerator)
  (stateComp  : StateComputer)
  where

  -- TODO-2: Requires refinement
  postulate
   contract' : EitherD-weakestPre (ConsensusProvider.startConsensus-ed-abs
                                    nodeConfig now payload liws sk needFetch propGen stateComp)
                                  (InitContract nothing)
