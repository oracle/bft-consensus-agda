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

module LibraBFT.Impl.Consensus.RoundManager where

  open RWST-do

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

  fakeProcessProposalMsg : Instant → ProposalMsg → LBFT Unit
  fakeProcessProposalMsg inst pm = do
    st ← get
    xx ← use rmHighestQC   -- Not used; just a demonstration that our RoundManager-specific "use" works
    modify' rmHighestQC xx -- Similarly for modify'
    let RoundManager∙new rm rmc rmw = st
        𝓔  = α-EC (rm , rmc)
        e  = rm ^∙ rmEpoch
        nr = suc (rm ^∙ rmLastVotedRound)
        uv = Vote∙new
                    (VoteData∙new (fakeBlockInfo e nr pm) (fakeBlockInfo e 0 pm))
                    fakeAuthor
                    (fakeLedgerInfo (fakeBlockInfo e nr pm) pm)
                    fakeSig
                    nothing
        sv = record uv { ₋vSignature = sign ⦃ sig-Vote ⦄ uv fakeSK}
        bt = rmw ^∙ (lBlockTree 𝓔)
        si = SyncInfo∙new (₋btHighestQuorumCert bt) (₋btHighestCommitCert bt)
        rm' = rm [ rmLastVotedRound := nr ]
        st' = RoundManager∙new rm' (RoundManagerEC-correct-≡ (₋rmEC st) rm' refl rmc)
                                   (subst RoundManagerWithEC (α-EC-≡ rm rm' refl refl rmc) rmw)
    put st'
    tell1 (SendVote (VoteMsg∙new sv si) (fakeAuthor ∷ []))
    pure unit

  processVote : Instant → VoteMsg → LBFT Unit
  processVote now msg = pure unit

  ------------------------------------------------------------------------------
  ensureRoundAndSyncUp : Instant → Round → SyncInfo → Author → Bool →
                         LBFT (Unit ⊎ Bool)
  ensureRoundAndSyncUp now messageRound syncInfo author helpRemote = pure (inj₁ unit)

  processProposal : Block → LBFT Unit
  processProposal b = pure unit

  -- external entry point
  processProposalMsg : Instant → Author → ProposalMsg → LBFT Unit
  processProposalMsg now from pm
     with pm ^∙ pmProposer
  ...| nothing = pure unit -- errorExit "ProposalMsg does not have an author"
  ...| just auth =
    ensureRoundAndSyncUp now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo) auth true >>= λ where
      (inj₁ _) → -- log error
        pure unit
      (inj₂ true) → processProposal (pm ^∙ pmProposal)
      (inj₂ false) → do
        -- dropping proposal for old round
        pure unit

