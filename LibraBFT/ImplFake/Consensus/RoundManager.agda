{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Prelude
open import Optics.All


-- This is a minimal/fake example handler that obeys the VotesOnce rule, enabling us to start
-- exploring how we express the algorithm and prove properties about it.  It simply sends a vote for
-- 1 + its LatestVotedRound, and increments its LatestVotedRound.  It is called RoundManager for
-- historical reasons, because this what a previous version of LibraBFT called its main handler;
-- this will be updated when we move towards modeling a more recent implementation.

module LibraBFT.ImplFake.Consensus.RoundManager where

processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
processCommitM finalityProof = pure []

fakeAuthor : Author
fakeAuthor = 0

fakeBlockInfo : Epoch → Round → ProposalMsg → BlockInfo
fakeBlockInfo eid rnd pm = BlockInfo∙new eid rnd (pm ^∙ pmProposal ∙ bId)

fakeLedgerInfo : BlockInfo → ProposalMsg → LedgerInfo
fakeLedgerInfo bi pm = LedgerInfo∙new bi (pm ^∙ pmProposal ∙ bId)

postulate -- TODO-1: these are temporary scaffolding for the fake implementation
  fakeSK  : SK
  fakeSig : Signature

processProposalMsg : Instant → ProposalMsg → LBFT Unit
processProposalMsg inst pm = do
  rm ← get
  --xx ← use rmHighestQC   -- Not used; just a demonstration that our RoundManager-specific "use" works
  --rmHighestQC ∙= xx -- Similarly for modify'
  let e  = rm ^∙ rmEpoch
      nr = suc (rm ^∙ rmLastVotedRound)
      uv = Vote∙new
                  (VoteData∙new (fakeBlockInfo e nr pm) (fakeBlockInfo e 0 pm))
                  fakeAuthor
                  (fakeLedgerInfo (fakeBlockInfo e nr pm) pm)
                  fakeSig
                  nothing
      sv = record uv { _vSignature = sign ⦃ sig-Vote ⦄ uv fakeSK}
      bt = rm ^∙ lBlockTree
      si = SyncInfo∙new (_btHighestQuorumCert bt) (_btHighestCommitCert bt)
      rm' = rm & rmLastVotedRound ∙~ nr
  put rm'
  tell1 (SendVote (VoteMsg∙new sv si) (fakeAuthor ∷ []))
  pure unit

processVote : Instant → VoteMsg → LBFT Unit
processVote now msg = pure unit

