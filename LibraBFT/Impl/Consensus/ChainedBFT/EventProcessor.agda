{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Hash
open import Optics.All

open RWST-do

-- This is a minimal/fake example handler that obeys the VotesOnce rule, enabling us to start
-- exploring how we express the algorithm and prove properties about it.  It simply sends a vote for
-- 1 + its LatestVotedRound, and increments its LatestVotedRound.  It is called EventProcessor for
-- historical reasons, because this what a previous version of LibraBFT called its main handler;
-- this will be updated when we move towards modeling a more recent implementation.

module LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
  processCommitM finalityProof = pure []

  fakeAuthor : Author
  fakeAuthor = 0

  fakeBlockInfo : EpochId → Round → ProposalMsg → BlockInfo
  fakeBlockInfo eid rnd pm = mkBlockInfo eid rnd (pm ^∙ pmProposal ∙ bId)

  fakeLedgerInfo : BlockInfo → ProposalMsg → LedgerInfo
  fakeLedgerInfo bi pm = mkLedgerInfo bi (pm ^∙ pmProposal ∙ bId)

  postulate
    fakeSK  : SK
    fakeSig : Signature

  processProposalMsg : Instant → ProposalMsg → LBFT Unit
  processProposalMsg inst pm = do
    st ← get
    let 𝓔  = α-EC ((₋epEC st) , (₋epEC-correct st))
        ix = EpochConfig.epochId 𝓔
        ep  = ₋epEC st
        epw = ₋epWithEC st
        epc = ₋epEC-correct st
        bt = epw ^∙ (lBlockTree 𝓔)
        nr = suc ((₋epEC st) ^∙ epLastVotedRound)
        uv = mkVote (mkVoteData (fakeBlockInfo ix nr pm) (fakeBlockInfo ix 0 pm))
                    fakeAuthor
                    (fakeLedgerInfo (fakeBlockInfo ix nr pm) pm)
                    fakeSig
                    (₋bSignature (₋pmProposal pm))
        sv =  record uv { ₋vSignature = sign ⦃ sig-Vote ⦄ uv fakeSK}
        si = mkSyncInfo (₋btHighestQuorumCert bt) (₋btHighestCommitCert bt)
        ep' = ep [ epLastVotedRound := nr ]
        epc2 = EventProcessorEC-correct-≡ (₋epEC st) ep' refl epc
        st' = record st { ₋epEC         = ep'
                        ; ₋epEC-correct = epc2
                        ; ₋epWithEC     = subst EventProcessorWithEC (α-EC-≡ ep ep' refl refl epc) epw
                        }
    put st'
    tell1 (SendVote (mkVoteMsg sv si) (fakeAuthor ∷ []))
    pure unit

  processVote : Instant → VoteMsg → LBFT Unit
  processVote now msg = pure unit
