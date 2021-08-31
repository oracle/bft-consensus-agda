{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block              as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                               using (String)

module LibraBFT.Impl.Consensus.ConsensusTypes.ProposalMsg where

verifyWellFormed : ProposalMsg → Either ErrLog Unit
verifyWellFormed self = do
  lcheck (not (Block.isNilBlock (self ^∙ pmProposal)))
         (here' ("Proposal for a NIL block" ∷ []))
  withErrCtx' ("Failed to verify ProposalMsg's block" ∷ [])
              (Block.verifyWellFormed (self ^∙ pmProposal))
  lcheck (self ^∙ pmProposal ∙ bRound >? 0)
         (here' ("Proposal for has round <= 0" ∷ []))
  lcheck (self ^∙ pmProposal ∙ bEpoch == self ^∙ pmSyncInfo ∙ siEpoch)
         (here' ("ProposalMsg has different epoch than SyncInfo" ∷ [])) -- lsSI (self ^∙ pmSyncInfo)

  lcheck (self ^∙ pmProposal ∙ bParentId == self ^∙ pmSyncInfo ∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biId)
         (here' ( "Proposal SyncInfo HQC CertifiedBlock id not eq to block parent id" ∷ []))
               -- lsSI (self ^∙ pmSyncInfo)
  let previousRound = self ^∙ pmProposal ∙ bRound ∸ 1 -- NOTE: monus usage
  let highestCertifiedRound =
        max (self ^∙ pmProposal ∙ bQuorumCert ∙ qcCertifiedBlock ∙ biRound)
            (maybeHsk 0 (_^∙ tcRound) (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert))
  lcheck (previousRound == highestCertifiedRound)
         (here' ("Proposal does not have a certified round" ∷ []))
               -- lsMTC (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert)
  lcheck (is-just (self ^∙ pmProposal ∙ bAuthor))
         (here' ("Proposal does not have an author" ∷ []))
  -- LBFT-DIFF : this check used to live in EventProcessor ∙ processProposedBlockM
  -- TODO: is it needed?
  -- Safety invariant: For any valid proposed block
  -- , its parent block == the block pointed to by its QC.
  lcheck (self ^∙ pmProposal ∙ bParentId == self ^∙ pmProposal ∙ bQuorumCert ∙ qcCertifiedBlock ∙ biId)
         (here' ("parent id /= qcCB" ∷ [])) -- show (self ^∙ pmProposal)
 where
  here' : List String → List String
  here' t = "ProposalMsg" ∷ "verifyWellFormed" {-∷ lsPM self-} ∷ t


verify : ProposalMsg → ValidatorVerifier → Either ErrLog Unit
verify self validator = do
  Block.validateSignature    (self ^∙ pmProposal)                        validator
  TimeoutCertificate.verify' (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert) validator
  verifyWellFormed self

