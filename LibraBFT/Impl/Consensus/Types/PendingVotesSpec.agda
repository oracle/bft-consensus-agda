{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                                       as Map
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote               as Vote
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Consensus.Types.PendingVotes                as PendingVotes
open import LibraBFT.Impl.Handle                                      as Handle
open import LibraBFT.Impl.Types.CryptoProxies                         as CryptoProxies
open import LibraBFT.Impl.Types.LedgerInfoWithSignatures              as LedgerInfoWithSignatures
open import LibraBFT.Impl.Types.ValidatorSigner                       as ValidatorSigner
open import LibraBFT.Impl.Types.ValidatorVerifier                     as ValidatorVerifier
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.Fin as Fin
open import Data.Vec as Vec using (Vec; lookup)

module LibraBFT.Impl.Consensus.Types.PendingVotesSpec where

open RWST-do

gs : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
gs = Vec.lookup

mkVote : ∀ {n : ℕ}
       → (Fin n → (LedgerInfo × VoteData))
       → Vec ValidatorSigner n
       → Fin n
       → Maybe LedgerInfo
       → (LedgerInfo × HashValue × Vote × HashValue)
mkVote randomLiVd signers i mli =
  let (li , voteData) = randomLiVd i
      hli             = hashLI li
      voteRoundAuthor = voteNew voteData (gs signers i ^∙ vsAuthor) li (gs signers i)
      hvli            = hashLI (voteRoundAuthor ^∙ vLedgerInfo)
   in (li , hli , voteRoundAuthor , hvli)
 where
  voteNew : VoteData → Author → LedgerInfo → ValidatorSigner → Vote
  voteNew voteData author ledgerInfoPlaceholder validatorSigner =
    let li        = record ledgerInfoPlaceholder { ₋liConsensusDataHash = hashVD voteData }
        signature = ValidatorSigner.sign validatorSigner li
     in Vote.newWithSignature voteData author li signature

iv : Vote → LBFT VoteReceptionResult
iv v = do
  s ← get
  let vv = rmGetEpochState s ^∙ esVerifier
  PendingVotes.insertVoteM v vv

{-
TODO : prove
Given a RoundManager that has
- an EpochState with a ValidatorVerifier with
  - 4 validators
  - ₋vvQuorumVotingPower of 3
- a RoundState that has a PendingVotes with
  - empty maps
  - nothing TC
Execution
- creates a non-timeout Vote and inserts it
Expect
- state
  - PendingVotes pvAuthorToVote to have that author/vote
  - PendingVOtes pvLiDigestToVotes to have digest to LIWS with author's signature
- the output to be 'QCVoteAdded 1'
-}
test-LBFT-PendingVotes-QC-aggregation-expect-QCVoteAdded-1
  : ∀ {n : ℕ}
  → Fin n -- TODO : want to create inside the function, not pass in
  → Vec ValidatorSigner n
  → (Fin n → (LedgerInfo × VoteData))
  → LBFT VoteReceptionResult
test-LBFT-PendingVotes-QC-aggregation-expect-QCVoteAdded-1 n signers randomLiVd = do
  let (li0 , _hli0 , voteRound1Author0 , _hvli0) = mkVote randomLiVd signers n nothing
  iv voteRound1Author0
