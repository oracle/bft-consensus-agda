{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.BlockData  as BlockData
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Types.BlockInfo                     as BlockInfo
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

isGenesisBlock : Block → Bool
isGenesisBlock b = BlockData.isGenesisBlock (b ^∙ bBlockData)

isNilBlock : Block → Bool
isNilBlock b = BlockData.isNilBlock (b ^∙ bBlockData)

postulate
  -- This is not needed until epoch change is implements/supported.
  makeGenesisBlockFromLedgerInfo : LedgerInfo → Block

newProposalFromBlockDataAndSignature : BlockData → Signature → Block
newProposalFromBlockDataAndSignature blockData signature =
  Block∙new (hashBD blockData) blockData (just signature)

validateSignature : Block → ValidatorVerifier → Either ErrLog Unit
validateSignature self validator = case self ^∙ bBlockData ∙ bdBlockType of λ where
  Genesis             → Left fakeErr -- (ErrL (here' ["do not accept genesis from others"]))
  NilBlock            → QuorumCert.verify (self ^∙ bQuorumCert) validator
  (Proposal _ author) → do
    fromMaybeM
      (Left fakeErr) -- (ErrL (here' ["Missing signature in Proposal"])))
      (pure (self ^∙ bSignature)) >>= λ sig -> withErrCtx' (here' [])
        (ValidatorVerifier.verify validator author (self ^∙ bBlockData) sig)
    QuorumCert.verify (self ^∙ bQuorumCert) validator
 where
  here' : List String.String → List String.String
  here' t = "Block" ∷ "validateSignatures" {-∷ lsB self-} ∷ t

verifyWellFormed : Block → Either ErrLog Unit
verifyWellFormed self = do
  lcheck (not (isGenesisBlock self))
         (here' ("Do not accept genesis from others" ∷ []))
  let parent = self ^∙ bQuorumCert ∙ qcCertifiedBlock
  lcheck (parent ^∙ biRound <? self ^∙ bRound)
         (here' ("Block must have a greater round than parent's block" ∷ []))
  lcheck (parent ^∙ biEpoch == self ^∙ bEpoch)
         (here' ("block's parent should be in the same epoch" ∷ []))
  lcheck (not (BlockInfo.hasReconfiguration parent)
          ∨ maybeHsk true payloadIsEmpty (self ^∙ bPayload))
         (here' ("Reconfiguration suffix should not carry payload" ∷ []))
  -- timestamps go here -- Haskell removed them
  lcheck (not (self ^∙ bQuorumCert ∙ qcEndsEpoch))
         (here' ("Block cannot be proposed in an epoch that has ended" ∷ []))
  lcheck (self ^∙ bId == hashBD (self ^∙ bBlockData))
         (here' ("Block id hash mismatch" ∷ []))
 where
  here' : List String.String → List String.String
  here' t = "Block" ∷ "verifyWellFormed" {-∷ lsB self-} ∷ t
