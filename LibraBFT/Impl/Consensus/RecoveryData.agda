{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.LedgerRecoveryData as LedgerRecoveryData
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.RecoveryData where

findBlocksToPrune
  : HashValue → List Block → List QuorumCert
  → (List HashValue × List Block × List QuorumCert)

new
  : Maybe Vote
  → LedgerRecoveryData
  → List Block
  → RootMetadata
  → List QuorumCert
  → Maybe TimeoutCertificate
  → RecoveryData
new lastVote storageLedger blocks0 rootMetadata quorumCerts0 highestTimeoutCertificate =
  let (root@(RootInfo∙new rb _ _) , blocks1 , quorumCerts1)
            = LedgerRecoveryData.findRoot blocks0 quorumCerts0 storageLedger
      (blocksToPrune , blocks , quorumCerts)
            = findBlocksToPrune (rb ^∙ bId) blocks1 quorumCerts1
      epoch = rb ^∙ bEpoch
   in mkRecoveryData
      (case lastVote of λ where
        (just v) → if-dec v ^∙ vEpoch ≟ epoch then just v else nothing
        nothing  → nothing)
      root
      rootMetadata
      blocks
      quorumCerts
      (just blocksToPrune)
      (case highestTimeoutCertificate of λ where
        (just tc) → if-dec tc ^∙ tcEpoch ≟ epoch then just tc else nothing
        nothing   → nothing)

-- TODO (the "TODO" is in the Haskell code)
findBlocksToPrune _rootId blocks quorumCerts = ([] , blocks , quorumCerts)
