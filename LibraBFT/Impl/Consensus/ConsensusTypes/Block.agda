{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.BlockData as BlockData
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.Block where

postulate
  validateSignature : Block → ValidatorVerifier → Either ErrLog Unit

genBlockInfo : Block → HashValue → Version → Maybe EpochState → BlockInfo
genBlockInfo b executedStateId version nextEpochState = BlockInfo∙new
  (b ^∙ bEpoch) (b ^∙ bRound) (b ^∙ bId) executedStateId version nextEpochState

isNilBlock : Block → Bool
isNilBlock b = BlockData.isNilBlock (b ^∙ bBlockData)
