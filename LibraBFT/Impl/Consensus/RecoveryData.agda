{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.Consensus.RecoveryData where

postulate
 new
  : Maybe Vote
  → LedgerRecoveryData
  → List Block
  → RootMetadata
  → List QuorumCert
  → Maybe TimeoutCertificate
  → RecoveryData
-- TODO-1 : IMPLEMENT THE FOLLOWING
{-
new lastVote storageLedger blocks0 rootMetadata quorumCerts0 highestTimeoutCertificate =
  let (root@(RootInfo rb _ _), blocks1, quorumCerts1)
            = LedgerRecoveryData.findRoot blocks0 quorumCerts0 storageLedger
      (blocksToPrune, blocks, quorumCerts)
            = findBlocksToPrune (rb^.bId) blocks1 quorumCerts1
      epoch = rb^.bEpoch
   in RecoveryData
      (case lastVote of Just v | v^.vEpoch == epoch → Just v; _ → Nothing)
      root
      rootMetadata
      blocks
      quorumCerts
      (Just blocksToPrune)
      (case highestTimeoutCertificate of Just tc | tc^.tcEpoch == epoch → Just tc; _ → Nothing)
-}
