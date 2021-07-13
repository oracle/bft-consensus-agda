{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
import      LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData as VoteData
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures    as LedgerInfoWithSignatures
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert where

  verify : QuorumCert → ValidatorVerifier → Either ErrLog Unit
  verify self validator = do
    let voteHash = hashVD (self ^∙ qcVoteData)
    lcheck (self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash == voteHash)
           -- (here ["Quorum Cert's hash mismatch LedgerInfo"])

    if (self ^∙ qcCertifiedBlock ∙ biRound == 0)
      -- TODO-?: It would be nice not to require the parens around the do block
      then (do
        lcheck (self ^∙ qcParentBlock == self ^∙ qcCertifiedBlock)
               -- (here ["Genesis QC has inconsistent parent block with certified block"])
        lcheck (self ^∙ qcCertifiedBlock == self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo)
               -- (here ["Genesis QC has inconsistent commit block with certified block"])
        lcheck (Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) == 0)
               -- (here ["Genesis QC should not carry signatures"])
        )
      else do
        -- TODO: withErrCtx'
        (LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo) validator)
        VoteData.verify (self ^∙ qcVoteData)
