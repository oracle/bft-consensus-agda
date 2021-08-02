{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore         as BlockStore
import      LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo         as SyncInfo
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote             as Vote
import      LibraBFT.Impl.Consensus.PendingVotes                    as PendingVotes
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-1 as ECP-LBFT-OBM-Diff-1
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Rust.Duration
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

module LibraBFT.Impl.Consensus.Liveness.RoundState where

------------------------------------------------------------------------------

postulate
  setupTimeoutM : Instant → LBFT Duration

------------------------------------------------------------------------------

processLocalTimeoutM : Instant → Epoch → Round → LBFT Bool
processLocalTimeoutM now obmEpoch round = do
  currentRound ← use (lRoundState ∙ rsCurrentRound)
  if-RWST round /= currentRound
    then pure false
    else do
      void (setupTimeoutM now) -- setup the next timeout
      ECP-LBFT-OBM-Diff-1.e_RoundState_processLocalTimeoutM obmEpoch round

------------------------------------------------------------------------------

maybeAdvanceRound : Round → SyncInfo → Maybe (Round × NewRoundReason)

processCertificatesM : Instant → SyncInfo → LBFT (Maybe NewRoundEvent)
processCertificatesM now syncInfo =
  logEE ("RoundState" ∷ "processCertificatesM" {-∷ lsSI syncInfo-} ∷ []) $ do
  rshcr <- use (lRoundState ∙ rsHighestCommittedRound)
  when (syncInfo ^∙ siHighestCommitRound <? rshcr) $ do
    lRoundState ∙ rsHighestCommittedRound ∙= (syncInfo ^∙ siHighestCommitRound)
    logInfo fakeInfo -- InfoUpdateHighestCommittedRound (syncInfo^.siHighestCommitRound)
  rscr ← use (lRoundState ∙ rsCurrentRound)
  maybeS-RWST (maybeAdvanceRound rscr syncInfo) (pure nothing) $ λ (pcr' , reason) → do
    lRoundState ∙ rsCurrentRound ∙= pcr'
    lRoundState ∙ rsPendingVotes ∙= PendingVotes∙new
    lRoundState ∙ rsVoteSent     ∙= nothing
    timeout                       ← setupTimeoutM now
    pure (just (NewRoundEvent∙new pcr' reason timeout))

maybeAdvanceRound currentRound syncInfo =
  let newRound = SyncInfo.highestRound syncInfo + 1
   in if-dec newRound >? currentRound
      then just (newRound , (if is-nothing (syncInfo ^∙ siHighestTimeoutCert) then QCReady else TOReady))
      else nothing

------------------------------------------------------------------------------

insertVoteM : Vote → ValidatorVerifier → LBFT VoteReceptionResult
insertVoteM vote verifier = do
  currentRound ← use (lRoundState ∙ rsCurrentRound)
  if-RWST vote ^∙ vVoteData ∙ vdProposed ∙ biRound == currentRound
    then PendingVotes.insertVoteM vote verifier
    else pure (UnexpectedRound (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) currentRound)

------------------------------------------------------------------------------

recordVoteM : Vote → LBFT Unit
recordVoteM v = rsVoteSent-rm ∙= just v

