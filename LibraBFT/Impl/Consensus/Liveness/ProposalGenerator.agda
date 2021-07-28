{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode                             as Encode
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.ConsensusTypes.BlockData as BlockData
open import LibraBFT.Impl.Types.BlockInfo                    as BlockInfo
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.Liveness.ProposalGenerator where

ensureHighestQuorumCertM : Round → LBFT (Either ErrLog QuorumCert)

postulate
  generateNilBlockM : Round → LBFT (Either ErrLog Block)

generateProposalM : Instant → Round → LBFT (Either ErrLog BlockData)
generateProposalM _now round = do
  lrg ← use (lProposalGenerator ∙ pgLastRoundGenerated)
  if-RWST lrg <?ℕ round
    then (do
      lProposalGenerator ∙ pgLastRoundGenerated ∙= round
      ensureHighestQuorumCertM round ∙?∙ λ hqc -> do
        payload ← if-RWST BlockInfo.hasReconfiguration (hqc ^∙ qcCertifiedBlock)
                      -- IMPL-DIFF : create a fake TX
                      then pure (Encode.encode 0) -- (Payload [])
                      else pure (Encode.encode 0) -- use pgTxnManager <*> use (rmEpochState ∙ esEpoch) <*> pure round
        use (lRoundManager ∙ pgAuthor) >>= λ where
          nothing       → bail fakeErr -- ErrL (here ["lRoundManager.pgAuthor", "Nothing"])
          (just author) →
            ok (BlockData.newProposal payload author round {-pure blockTimestamp <*>-} hqc))
    else bail fakeErr
-- where
--  here t = "ProposalGenerator" ∷ "generateProposal" ∷ t

ensureHighestQuorumCertM round = do
  hqc ← use (lBlockStore ∙ bsHighestQuorumCert)
  ifM‖ (hqc ^∙ qcCertifiedBlock ∙ biRound) ≥?ℕ round ≔
       bail fakeErr {- ErrL (here [ "given round is lower than hqc round"
                                  , show (hqc^.qcCertifiedBlock.biRound) ]) -}
     ‖ hqc ^∙ qcEndsEpoch ≔
       bail fakeErr {-ErrEpochEndedNoProposals (here ["further proposals not allowed"])-}
     ‖ otherwise≔
       ok hqc
-- where
--  here t = "ProposalGenerator":"ensureHighestQuorumCertM":lsR round:t

