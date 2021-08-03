{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS
import      LibraBFT.Impl.Consensus.ConsensusTypes.BlockData  as BlockData
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Types.ValidatorVerifier             as ValidatorVerifier
open import LibraBFT.Impl.OBM.Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                       as String

module LibraBFT.Impl.Consensus.ConsensusTypes.Block where

genBlockInfo : Block → HashValue → Version → Maybe EpochState → BlockInfo
genBlockInfo b executedStateId version nextEpochState = BlockInfo∙new
  (b ^∙ bEpoch) (b ^∙ bRound) (b ^∙ bId) executedStateId version nextEpochState

isNilBlock : Block → Bool
isNilBlock b = BlockData.isNilBlock (b ^∙ bBlockData)

newProposalFromBlockDataAndSignature : BlockData → Signature → Block
newProposalFromBlockDataAndSignature blockData signature =
  Block∙new (hashBD blockData) blockData (just signature)

validateSignature : Block → ValidatorVerifier → Either ErrLog Unit
validateSignature self validator = case self ^∙ bBlockData ∙ bdBlockType of λ where
  Genesis             → Left fakeErr -- (ErrL (here' ["do not accept genesis from others"]))
  NilBlock            → QuorumCert.verify (self ^∙ bQuorumCert) validator
  (Proposal _ author) → do
    fromMaybeE
      (Left fakeErr) -- (ErrL (here' ["Missing signature in Proposal"])))
      (self ^∙ bSignature) >>= λ sig -> withErrCtx' (here' [])
        (ValidatorVerifier.verify validator author (self ^∙ bBlockData) sig)
    QuorumCert.verify (self ^∙ bQuorumCert) validator
 where
  here' : List String.String → List String.String
  here' t = "Block" ∷ "validateSignatures" {-∷ lsB self-} ∷ t
