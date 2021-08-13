{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                                       as Map
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote               as Vote
open import LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.Types.CryptoProxies                         as CryptoProxies
open import LibraBFT.Impl.Types.LedgerInfoWithSignatures              as LedgerInfoWithSignatures
open import LibraBFT.Impl.Types.ValidatorVerifier                     as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.PendingVotes where

insertVoteM : Vote → ValidatorVerifier → LBFT VoteReceptionResult
insertVoteM vote vv = do
  let liDigest = hashLI (vote ^∙ vLedgerInfo)
  atv          ← use (lPendingVotes ∙ pvAuthorToVote)
  caseMD Map.lookup (vote ^∙ vAuthor) atv of λ where
    (just previouslySeenVote) →
      ifD liDigest ≟Hash (hashLI (previouslySeenVote ^∙ vLedgerInfo))
      then (do
        let newTimeoutVote = Vote.isTimeout vote ∧ not (Vote.isTimeout previouslySeenVote)
        if not newTimeoutVote
          then pure DuplicateVote
          else continue1 liDigest)
      else
        pure EquivocateVote
    nothing →
      continue1 liDigest

 where

  continue2 : U64 → LBFT VoteReceptionResult

  continue1 : HashValue → LBFT VoteReceptionResult
  continue1 liDigest = do
    pv            ← use lPendingVotes
    lPendingVotes ∙ pvAuthorToVote %= Map.kvm-insert-Haskell (vote ^∙ vAuthor) vote
    let liWithSig = CryptoProxies.addToLi (vote ^∙ vAuthor) (vote ^∙ vSignature)
                      (fromMaybe (LedgerInfoWithSignatures∙new (vote ^∙ vLedgerInfo) Map.empty)
                                 (Map.lookup liDigest (pv ^∙ pvLiDigestToVotes)))
    lPendingVotes ∙ pvLiDigestToVotes %= Map.kvm-insert-Haskell liDigest liWithSig
    case⊎D ValidatorVerifier.checkVotingPower vv (Map.kvm-keys (liWithSig ^∙ liwsSignatures)) of λ where
      (Right unit) →
        pure (NewQuorumCertificate (QuorumCert∙new (vote ^∙ vVoteData) liWithSig))
      (Left (ErrVerify (TooLittleVotingPower votingPower _))) →
        continue2 votingPower
      (Left _) →
        pure VRR_TODO

  continue2 qcVotingPower =
    caseMD vote ^∙ vTimeoutSignature of λ where
      (just timeoutSignature) → do
        pv            ← use lPendingVotes
        let partialTc = TimeoutCertificate.addSignature (vote ^∙ vAuthor) timeoutSignature
                          (fromMaybe (TimeoutCertificate∙new (Vote.timeout vote))
                                     (pv ^∙ pvMaybePartialTC))
        lPendingVotes ∙ pvMaybePartialTC %= const (just partialTc)
        case⊎D ValidatorVerifier.checkVotingPower vv (Map.kvm-keys (partialTc ^∙ tcSignatures)) of λ where
          (Right unit) →
            pure (NewTimeoutCertificate partialTc)
          (Left (ErrVerify (TooLittleVotingPower votingPower _))) →
            pure (TCVoteAdded votingPower)
          (Left _) →
            pure VRR_TODO
      nothing →
        pure (QCVoteAdded qcVotingPower)




