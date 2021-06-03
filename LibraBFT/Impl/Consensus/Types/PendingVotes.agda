{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap       as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.Types.PendingVotes where

open RWST-do

AuthorName : Set
AuthorName = Author

U64 : Set
U64 = ℕ

Usize : Set
Usize = ℕ

data VoteReceptionResult : Set where
  QCVoteAdded           : U64 →                VoteReceptionResult
  TCVoteAdded           : U64 →                VoteReceptionResult
  DuplicateVote         :                      VoteReceptionResult
  EquivocateVote        :                      VoteReceptionResult
  NewQuorumCertificate  : QuorumCert →         VoteReceptionResult
  NewTimeoutCertificate : TimeoutCertificate → VoteReceptionResult
  UnexpectedRound       : Round → Round →      VoteReceptionResult
  VRR_TODO              :                      VoteReceptionResult

data VerifyError : Set where
  UnknownAuthor        : AuthorName →    VerifyError
  TooLittleVotingPower : U64 → U64 →     VerifyError
  TooManySignatures    : Usize → Usize → VerifyError
  InvalidSignature     :                 VerifyError

-- TODO Vote
timeout : Vote → Timeout
timeout v = Timeout∙new (v ^∙ vVoteData ∙ vdProposed ∙ biEpoch) (v ^∙ vVoteData ∙ vdProposed ∙ biRound)

-- TODO Vote
isTimeout : Vote → Bool
isTimeout v with v ^∙ vTimeoutSignature
... | (just _) = true
... | _        = false

-- TODO ValidatorVerifier
checkVotingPower : ValidatorVerifier → List AccountAddress → VerifyError ⊎ Unit
checkVotingPower self authors = inj₁ (TooLittleVotingPower 0 0)

-- TODO TimeoutCertificate
TOaddSignature : Author → Signature → TimeoutCertificate → TimeoutCertificate
TOaddSignature a s tc with Map.lookup a (tc ^∙ tcSignatures)
... | (just existing) = mkTimeoutCertificate
                          (tc ^∙ tcTimeout)
                          (Map.kvm-insert-Haskell a s (tc ^∙ tcSignatures))
... | nothing         = mkTimeoutCertificate
                          (tc ^∙ tcTimeout)
                          (Map.kvm-insert-Haskell a s Map.empty)

-- TODO LedgerInfoWithSignatures
addSignature : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addSignature validator sig liws
    with Map.lookup validator (liws ^∙ liwsSignatures)
... | (just existing) = LedgerInfoWithSignatures∙new
                          (liws ^∙ liwsLedgerInfo)
                          (Map.kvm-insert-Haskell validator sig (liws ^∙ liwsSignatures))
... | nothing         = LedgerInfoWithSignatures∙new
                          (liws ^∙ liwsLedgerInfo)
                          (Map.kvm-insert-Haskell validator sig Map.empty)

-- TODO LBFT.Types.CryptoProxies
addToLi : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addToLi = {-LedgerInfoWithSignatures.-}addSignature

insertVoteM : Vote → ValidatorVerifier → LBFT VoteReceptionResult
insertVoteM vote vv = do
  let liDigest = hashLI (vote ^∙ vLedgerInfo)
  atv          ← use (lPendingVotes ∙ pvAuthorToVote)
  case (Map.lookup (vote ^∙ vAuthor) atv) of λ where
    (just previouslySeenVote) →
      if ⌊ liDigest ≟Hash (hashLI (previouslySeenVote ^∙ vLedgerInfo)) ⌋
      then (do
        let newTimeoutVote = {-Vote.-}isTimeout vote ∧ not ({-Vote.-}isTimeout previouslySeenVote)
        (if (not newTimeoutVote)
         then (pure DuplicateVote)
         else (continue1 liDigest)))
      else (pure EquivocateVote)
    nothing →
      continue1 liDigest

 where

  continue2 : U64 → LBFT VoteReceptionResult

  continue1 : HashValue → LBFT VoteReceptionResult
  continue1 liDigest = do
    pv            ← use lPendingVotes
    (lPendingVotes ∙ pvAuthorToVote) %=
      λ m → Map.kvm-insert-Haskell (vote ^∙ vAuthor) vote m
    let liWithSig = {-CryptoProxies.-}addToLi (vote ^∙ vAuthor) (vote ^∙ vSignature)
                      (fromMaybe (LedgerInfoWithSignatures∙new (vote ^∙ vLedgerInfo) Map.empty)
                                 (Map.lookup liDigest (pv ^∙ pvLiDigestToVotes)))
        dtv       = Map.kvm-insert-Haskell liDigest liWithSig (pv ^∙ pvLiDigestToVotes)
    (case {-ValidatorVerifier.-}checkVotingPower vv (Map.kvm-keys (liWithSig ^∙ liwsSignatures)) of
     λ { (inj₂ Unit) →
           pure DuplicateVote
       ; (inj₁ (TooLittleVotingPower votingPower _)) →
           continue2 votingPower
       ; (inj₁ _) →
           pure VRR_TODO })

  continue2 qcVotingPower = do
    (case (vote ^∙ vTimeoutSignature) of
     λ { (just timeoutSignature) → do
           pv            ← use (lRoundState ∙ rsPendingVotes) -- TODO use lPendingVotes
           let partialTc = {-TimeoutCertificate.-}TOaddSignature (vote ^∙ vAuthor) timeoutSignature
                             (fromMaybe (TimeoutCertificate∙new ({-Vote.-}timeout vote))
                                        (pv ^∙ pvMaybePartialTC))
           modify' (lRoundState ∙ rsPendingVotes ∙ pvMaybePartialTC) (just partialTc)
           (case {-ValidatorVerifier.-}checkVotingPower
                   vv (Map.kvm-keys (partialTc ^∙ tcSignatures)) of
            λ { (inj₂ Unit) →
                  pure (NewTimeoutCertificate partialTc)
              ; (inj₁ (TooLittleVotingPower votingPower _)) →
                  pure (TCVoteAdded votingPower)
              ; (inj₁ _) →
                  pure VRR_TODO })
       ; nothing →
           pure (QCVoteAdded qcVotingPower) })




