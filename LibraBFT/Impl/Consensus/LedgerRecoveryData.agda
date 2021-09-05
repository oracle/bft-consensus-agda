{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.LedgerRecoveryData where

postulate -- TODO-2: compareX, sortBy, findIndex, deleteAt, find
  compareX  : (Epoch × Round) → (Epoch × Round) → Ordering
  sortBy    : (Block → Block → Ordering) → List Block → List Block
  findIndex : (Block → Bool) → List Block → Maybe ℕ
  deleteAt  : ℕ → List Block → List Block
  find      : (QuorumCert → Bool) → List QuorumCert -> Maybe QuorumCert

findRoot : List Block → List QuorumCert → LedgerRecoveryData
         → Either ErrLog (RootInfo × List Block × List QuorumCert)
findRoot blocks0 quorumCerts0 (LedgerRecoveryData∙new storageLedger) = do
  (rootId , (blocks1 , quorumCerts)) ←
        if storageLedger ^∙ liEndsEpoch
        then (do
          genesis       ← Block.makeGenesisBlockFromLedgerInfo storageLedger
          let genesisQC = QuorumCert.certificateForGenesisFromLedgerInfo storageLedger (genesis ^∙ bId)
          pure (genesis ^∙ bId , (genesis ∷ blocks0 , genesisQC ∷ quorumCerts0)))
        else
          pure (storageLedger ^∙ liConsensusBlockId , (blocks0 , quorumCerts0))
  let sorter : Block → Block → Ordering
      sorter bl br = compareX (bl ^∙ bEpoch , bl ^∙ bRound) (br ^∙ bEpoch , br ^∙ bRound)
      sortedBlocks = sortBy sorter blocks1
  rootIdx          ← maybeS
        (findIndex (λ x → x ^∙ bId == rootId) sortedBlocks)
        (Left fakeErr) -- ["unable to find root", show rootId]
        (pure ∘ id)
  rootBlock         ← maybeS
        (sortedBlocks !? rootIdx)
        (Left fakeErr) -- ["sortedBlocks !? rootIdx"]
        (pure ∘ id)
  let blocks       = deleteAt rootIdx sortedBlocks
  rootQuorumCert   ← maybeS
        (find (λ x → x ^∙ qcCertifiedBlock ∙ biId == rootBlock ^∙ bId) quorumCerts)
        (Left fakeErr) -- ["No QC found for root", show rootId]
        (pure ∘ id)
  rootLedgerInfo   ← maybeS
        (find (λ x → x ^∙ qcCommitInfo ∙ biId == rootBlock ^∙ bId) quorumCerts)
        (Left fakeErr) -- ["No LI found for root", show rootId]
        (pure ∘ id)
  pure (RootInfo∙new rootBlock rootQuorumCert rootLedgerInfo , blocks , quorumCerts)
{-
 where
  here t = "LedgerRecoveryData":"findRoot":t
  deleteAt idx xs = lft ++ tail rgt where (lft, rgt) = splitAt idx xs
  tail = \case [] -> []; (_:xs) -> xs
-}
