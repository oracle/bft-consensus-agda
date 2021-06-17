{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore as BlockStore
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote     as Vote
open import LibraBFT.Impl.Consensus.Types.PendingVotes      as PendingVotes hiding (insertVoteM)
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

module LibraBFT.Impl.Consensus.Liveness.RoundState where

open RWST-do

------------------------------------------------------------------------------

processCertificatesM : Instant → SyncInfo → LBFT (Maybe NewRoundEvent)
processCertificatesM now syncInfo = do
  rshcr <- use (lRoundState ∙ rsHighestCommittedRound)
  if-dec (syncInfo ^∙ siHighestCommitRound <? rshcr) -- TODO : define and use 'when'
    then pure unit -- IMPL-TODO ((lRoundState ∙ rsHighestCommittedRound) :=  (syncInfo ^∙ siHighestCommitRound))
    else pure unit
  pure nothing

------------------------------------------------------------------------------

insertVoteM : Vote → ValidatorVerifier → LBFT VoteReceptionResult
insertVoteM vote verifier = do
  currentRound ← use (lRoundState ∙ rsCurrentRound)
  if-dec vote ^∙ vVoteData ∙ vdProposed ∙ biRound ≟ℕ currentRound
    then PendingVotes.insertVoteM vote verifier
    else pure (UnexpectedRound (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) currentRound)
