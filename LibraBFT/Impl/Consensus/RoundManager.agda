{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId


-- This is a minimal/fake example handler that obeys the VotesOnce rule, enabling us to start
-- exploring how we express the algorithm and prove properties about it.  It simply sends a vote for
-- 1 + its LatestVotedRound, and increments its LatestVotedRound.  It is called RoundManager for
-- historical reasons, because this what a previous version of LibraBFT called its main handler;
-- this will be updated when we move towards modeling a more recent implementation.

module LibraBFT.Impl.Consensus.RoundManager
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open RWST-do

  processCommitM : LedgerInfoWithSignatures → LBFT (List ExecutedBlock)
  processCommitM finalityProof = pure []

  fakeAuthor : Author
  fakeAuthor = 0

  fakeBlockInfo : EpochId → Round → ProposalMsg → BlockInfo
  fakeBlockInfo eid rnd pm = mkBlockInfo eid rnd (pm ^∙ pmProposal ∙ bId)

  fakeLedgerInfo : BlockInfo → ProposalMsg → LedgerInfo
  fakeLedgerInfo bi pm = mkLedgerInfo bi (pm ^∙ pmProposal ∙ bId)

  postulate -- TODO-1: these are temporary scaffolding for the fake implementation
    fakeSK  : SK
    fakeSig : Signature

  processProposalMsg : Instant → ProposalMsg → LBFT Unit
  processProposalMsg inst pm = do
    st ← get
    let 𝓔  = α-EC ((₋rmEC st) , (₋rmEC-correct st))
        rm  = ₋rmEC st
        rmw = ₋rmWithEC st
        rmc = ₋rmEC-correct st
        bt = rmw ^∙ (lBlockTree 𝓔)
        nr = suc ((₋rmEC st) ^∙ rmLastVotedRound)
        ix = rm ^∙ rmEpoch
        uv = mkVote (mkVoteData (fakeBlockInfo ix nr pm) (fakeBlockInfo ix 0 pm))
                    fakeAuthor
                    (fakeLedgerInfo (fakeBlockInfo ix nr pm) pm)
                    fakeSig
                    (₋bSignature (₋pmProposal pm))
        sv =  record uv { ₋vSignature = sign ⦃ sig-Vote ⦄ uv fakeSK}
        si = mkSyncInfo (₋btHighestQuorumCert bt) (₋btHighestCommitCert bt)
        rm' = rm [ rmLastVotedRound := nr ]
        rmc2 = RoundManagerEC-correct-≡ (₋rmEC st) rm' refl rmc
        st' = record st { ₋rmEC         = rm'
                        ; ₋rmEC-correct = rmc2
                        ; ₋rmWithEC     = subst RoundManagerWithEC (α-EC-≡ rm rm' refl refl rmc) rmw
                        }
    put st'
    tell1 (SendVote (mkVoteMsg sv si) (fakeAuthor ∷ []))
    pure unit

  processVote : Instant → VoteMsg → LBFT Unit
  processVote now msg = pure unit
