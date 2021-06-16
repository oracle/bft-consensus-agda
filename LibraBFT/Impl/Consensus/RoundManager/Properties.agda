{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore       as BlockStore
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock  as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.RoundState           as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection     as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage     as PersistentLivenessStorage
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules       as SafetyRules
open import LibraBFT.Impl.Util.Util

open RWST-do

module LibraBFT.Impl.Consensus.RoundManager.Properties where
open import LibraBFT.Impl.Consensus.RoundManager

module FakeProcessProposalMsg where
  voteForCurrentEpoch : ∀ {ts pm pre vm αs}
                      → (SendVote vm αs) ∈ LBFT-outs (fakeProcessProposalMsg ts pm) pre
                      → (₋rmEC pre) ^∙ rmEpoch ≡ (unmetaVoteMsg vm) ^∙ vmVote ∙ vEpoch
  voteForCurrentEpoch (here refl) = refl

  -- The quorum certificates sent in SyncInfo with votes are those from the peer state.
  -- This is no longer used because matching m∈outs parameters to here refl eliminated the need for
  -- it, at least for our simple handler.  I'm keeping it, though, as it may be needed in future
  -- when the real handler will be much more complicated and this proof may no longer be trivial.
  procPMCerts≡ : ∀ {ts pm pre vm αs}
               → (SendVote vm αs) ∈ LBFT-outs (fakeProcessProposalMsg ts pm) pre
               → (unmetaVoteMsg vm) ^∙ vmSyncInfo ≡ SyncInfo∙new (₋rmHighestQC pre) (₋rmHighestCommitQC pre)
  procPMCerts≡ (here refl) = refl


module ExecuteAndVoteM (b : Block) where
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open import LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules
  open import LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties

  -- TODO-2: This should be proven "by construction", not directly.
  postulate
    noOuts
      : ∀ pre
        → RWST-weakestPre (executeAndVoteM b) (λ _ _ outs → outs ≡ []) unit pre

  VoteSrcCorrect = ConstructAndSignVoteM.VoteSrcCorrect

  c₃ : VoteWithMeta → LBFT (ErrLog ⊎ VoteWithMeta)
  c₃ vote =
    PersistentLivenessStorage.saveVoteM (unmetaVote vote)
    ∙?∙ λ _ → ok vote

  c₂ : ExecutedBlock → Round → Maybe Vote → Bool → LBFT (ErrLog ⊎ VoteWithMeta)
  c₂ eb cr vs so =
    ifM‖ is-just vs
         ≔ bail unit -- already voted this round
       ‖ so
         ≔ bail unit -- sync-only set
       ‖ otherwise≔ do
         let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
         SafetyRules.constructAndSignVoteM maybeSignedVoteProposal' {- ∙^∙ logging -}
           ∙?∙ c₃

  c₁ : ExecutedBlock → LBFT (ErrLog ⊎ VoteWithMeta)
  c₁ eb = do
    cr ← use (lRoundState ∙ rsCurrentRound)
    vs ← use (lRoundState ∙ rsVoteSent)
    so ← use lSyncOnly
    c₂ eb cr vs so

  voteSrcCorrect
    : ∀ pre → RWST-weakestPre (executeAndVoteM b) (VoteSrcCorrect pre) unit pre
  voteSrcCorrect pre =
    ExecuteAndInsertBlockM.contract b (RWST-weakestPre-ebindPost unit c₁ _) pre unit
      λ where
        eb blockStore ._ refl ._ refl cr cr≡ ._ refl vs vs≡ ._ refl so so≡ →
          (const unit) , (λ _ → (const unit)
          , (λ _ → vsc eb blockStore))
      where
      module _ (eb : ExecutedBlock) (blockStore : BlockStore _) where
        maybeSignedVoteProposal = ExecutedBlock.maybeSignedVoteProposal eb
        st₁ = rmSetBlockStore pre blockStore

        impl : ∀ r st outs
               → VoteSrcCorrect pre r st outs
               → RWST-weakestPre-ebindPost unit c₃ (VoteSrcCorrect pre) r st outs
        impl (inj₁ _) st outs pf = unit
        impl (inj₂ (VoteWithMeta∙new vote mvsNew)) st outs pf ._ refl =
          SaveVoteM.contract vote _ st unit λ where
            blockStore' unit _ → pf
        impl (inj₂ (VoteWithMeta∙new vote mvsLastVote)) st outs pf ._ refl =
          SaveVoteM.contract vote _ st unit (λ where blockStore₁ unit ._ → pf)

        vsc
          : RWST-weakestPre
              (SafetyRules.constructAndSignVoteM maybeSignedVoteProposal
                ∙?∙ c₃)
              (VoteSrcCorrect pre)
              unit st₁
        vsc =
          RWST-impl
            _ (RWST-weakestPre-ebindPost unit c₃ (VoteSrcCorrect pre))
            impl
            (SafetyRules.constructAndSignVoteM maybeSignedVoteProposal) unit st₁
            (ConstructAndSignVoteM.voteSrcCorrect maybeSignedVoteProposal pre st₁ refl)

module ProcessProposalM (proposal : Block) where
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  VoteSrcCorrect : RoundManager → LBFT-Post Unit
  VoteSrcCorrect pre x post outs =
    ∀ vm αs → SendVote vm αs ∈ outs → VoteSrcCorrectCod pre post (vm ^∙ mvmVoteWithMeta)

  c₁ : ErrLog ⊎ VoteWithMeta → LBFT Unit
  c₁ _r =
    caseM⊎ (_r) of λ where
      (inj₁ _) → pure unit
      (inj₂ vote) → do
        RoundState.recordVote (unmetaVote vote)
        si ← BlockStore.syncInfo
        recipient ← ProposerElection.getValidProposer
                      <$> use lProposerElection
                      <*> pure (proposal ^∙ bRound + 1)
        act (SendVote (VoteMsgWithMeta∙fromVoteWithMeta vote si) (recipient ∷ []))

  voteSrcCorrect
    : ∀ pre → RWST-weakestPre (processProposalM proposal) (VoteSrcCorrect pre) unit pre
  voteSrcCorrect pre ._ refl =
    IsValidProposalM.contract proposal _ pre λ where
      b _ refl →
        (λ where _ _ _ ())
        , λ _ → (λ where _ _ _ ())
          , λ _ → (λ where _ _ _ ())
            , λ _ → (λ where _ _ _ ())
              , (λ _ → vsc)
    where
    -- TODO-3: This is unprovable without knowing that `outs` is [], i.e., that
    -- `executeAndVoteM` produces no output.
    impl : ∀ x st outs
           → (outs ≡ [] × ExecuteAndVoteM.VoteSrcCorrect proposal pre x st outs)
           → RWST-weakestPre-bindPost unit c₁ (VoteSrcCorrect pre) x st outs
    proj₁ (impl x st .[] (refl , pf) .x refl) unit _ _ _ ()
    proj₂ (impl ._ st .[] (refl , pf) .(inj₂ _) refl) (VoteWithMeta∙new vote mvsNew) refl unit _ =
      GetSyncInfo.contract _ st λ where
        _ r _ _ _ _ _ _ _ _ _ _ _ .(VoteMsgWithMeta∙new (VoteMsg∙new vote r) mvsNew) .(_ ∷ []) (here refl) →
          pf
    proj₂ (impl ._ st .[] (refl , pf) .(inj₂ _) refl) (VoteWithMeta∙new vote mvsLastVote) refl unit _ =
      GetSyncInfo.contract _ st λ where
        _ r _ _ _ _ _ _ _ _ _ _ _ .(VoteMsgWithMeta∙new (VoteMsg∙new vote r) mvsLastVote) ._ (here refl) →
          pf

    vsc : RWST-weakestPre (executeAndVoteM proposal) _ unit pre
    vsc = RWST-impl _ _ impl (executeAndVoteM proposal) unit pre
            (RWST-× _ _ (executeAndVoteM proposal) unit pre
              (ExecuteAndVoteM.noOuts proposal pre)
              (ExecuteAndVoteM.voteSrcCorrect proposal pre))
           -- RWST-impl _ _ impl (executeAndVoteM proposal) unit pre
           -- {!!} -- (ExecuteAndVoteM.voteSrcCorrect proposal pre)

module ProcessProposalMsgM (now : Instant) (pm : ProposalMsg) where

  VoteSrcCorrect : RoundManager → LBFT-Post Unit
  VoteSrcCorrect pre x post outs =
    ∀ vm αs → SendVote vm αs ∈ outs → VoteSrcCorrectCod pre post (vm ^∙ mvmVoteWithMeta)

  Contract : RoundManager → LBFT-Post Unit
  Contract pre x post outs =
    ∀ m → m ∈ outs →
    ∃₂ λ vm αs → m ≡ SendVote vm αs × VoteSrcCorrectCod pre post (vm ^∙ mvmVoteWithMeta)

  postulate
    contract
      : ∀ pre → RWST-weakestPre (processProposalMsgM now pm) (Contract pre) unit pre

  contract! : ∀ pre
              → let x    = RWST-result (processProposalMsgM now pm) unit pre
                    post = RWST-post   (processProposalMsgM now pm) unit pre
                    outs = RWST-outs   (processProposalMsgM now pm) unit pre in
                Contract pre x post outs
  contract! pre = RWST-contract (processProposalMsgM now pm) (Contract pre) unit pre (contract pre)

{-
  m∈outs⇒ : ∀ {nm ts pm pre} → nm ∈ LBFT-outs (processProposalMsgM ts pm) pre
            → let messageRound = pm ^∙ pmProposal ∙ bRound
                  syncInfo     = pm ^∙ pmSyncInfo
                  currentRound = pre ^∙ lRoundState ∙ rsCurrentRound in
              Σ[ a ∈ Author ]
                (just a ≡ pm ^∙ pmProposer
                  × ¬ (messageRound < currentRound)
                  × nm ∈ LBFT-outs (ensureRoundAndSyncUpM-check₁ ts messageRound syncInfo a true
                                    >>= processProposalMsgM-check₁-cont ts pm a)
                                   pre)
  m∈outs⇒{nm}{ts}{pm}{pre} m∈outs
     with pm ^∙ pmProposer
  ... | just author
     with (pm ^∙ pmProposal ∙ bRound) <? (pre ^∙ lRoundState ∙ rsCurrentRound)
  ... | no proof = author , refl , proof , m∈outs

  voteSrcCorrect₁ : ∀ {ts pm pre vm αs}
                  → (SendVote vm αs) ∈ LBFT-outs (processProposalMsgM ts pm) pre
                  → (vm ^∙ mvmSrc) ≡ mvsLastVote
                  → let lastVote = pre ^∙ lPersistentSafetyStorage ∙ pssSafetyData ∙ sdLastVote
                    in just (unmetaVoteMsg vm ^∙ vmVote) ≡ lastVote
  voteSrcCorrect₁{ts}{pm}{pre}{vm}{αs} vm∈outs src≡LastVote
     with m∈outs⇒{ts = ts}{pm} vm∈outs
  ...| a , pmAuth , mr≥cr , m∈outs₁
     with (pm ^∙ pmProposal ∙ bRound) ≟ℕ (pre ^∙ lRoundState ∙ rsCurrentRound)
  ...| yes proof₁
     with pm ^∙ pmProposer
  ...| just a'
     with ProposerElection.getValidProposer (pre ^∙ lProposerElection) (pm ^∙ pmProposal ∙ bRound)
  ...| a“
     with a“ ≟ℕ a'
  ...| yes proof₂
     with BlockStore.getQuorumCertForBlock (pm ^∙ pmProposal ∙ bParentId) (rmGetBlockStore pre)
  ...| just _
     with BlockStore.getBlock (pm ^∙ pmProposal ∙ bParentId) (rmGetBlockStore pre)
  ... | just parentBlock
     with (parentBlock ^∙ ebRound) <?ℕ (pm ^∙ pmProposal ∙ bRound)
  ... | yes proof
     with BlockStoreSpec.executeAndInsertBlockM-noOutput (pm ^∙ pmProposal) pre
      |   BlockStoreSpec.executeAndInsertBlockM-RW       (pm ^∙ pmProposal) pre
  ... | noOuts | eaib-rw
     with LBFT-run (BlockStore.executeAndInsertBlockM (pm ^∙ pmProposal)) pre
  voteSrcCorrect₁ vm∈outs src≡LastVote
      | a , pmAuth , mr≥cr , m∈outs₁ | yes proof₁ | just a' | a“ | yes proof₂ | just _ | just parentBlock | yes proof | refl | eaib-rw | inj₁ _ , rm₁ , .[] =
      ⊥-elim (¬Any[] m∈outs₁)
  voteSrcCorrect₁{ts}{pm}{pre}{vm}{αs} vm∈outs src≡LastVote
      | a , pmAuth , mr≥cr , m∈outs₁ | yes proof₁ | just a' | a“ | yes proof₂ | just _ | just parentBlock | yes proof | refl | eaib-rw | inj₂ eb , rm₁ , .[]
      with rm₁ ^∙ lRoundState ∙ rsVoteSent
  ... | nothing
      with rm₁ ^∙ lSyncOnly
  ... | false
      with ExecutedBlock.maybeSignedVoteProposal eb
  ... | maybeSignedVoteProposal'
      with SafetyRulesSpec.constructAndSignVoteM-voteSrcCorrect maybeSignedVoteProposal' rm₁
  ... | csv-vsc
      with SafetyRulesSpec.constructAndSignVoteM-noOutput maybeSignedVoteProposal' rm₁
  ... | noOuts
      with LBFT-run (SafetyRules.constructAndSignVoteM maybeSignedVoteProposal') rm₁
  voteSrcCorrect₁ vm∈outs src≡LastVote
      | a , pmAuth , mr≥cr , m∈outs₁ | yes proof₁ | just a' | a“ | yes proof₂ | just _ | just parentBlock | yes proof | refl | eaib-rw | inj₂ eb , rm₁ , .[]
      | nothing | false | maybeSignedVoteProposal' | csv-vsc | refl | inj₂ mv , rm₂ , .[]
      with BlockStoreSpec.syncInfo-noOutput rm₂
  ... | noOuts
      with LBFT-run BlockStore.syncInfo rm₂
  voteSrcCorrect₁ vm∈outs src≡LastVote
      | a , pmAuth , mr≥cr , here refl | yes proof₁ | just a' | a“ | yes proof₂ | just _ | just parentBlock | yes proof | refl | eaib-rw | inj₂ eb , rm₁ , .[]
      | nothing | false | maybeSignedVoteProposal' | csv-vsc | refl | inj₂ mv , rm₂ , .[]
      | refl | si , rm₃ , .[] rewrite sym eaib-rw = csv-vsc src≡LastVote
-}

open FakeProcessProposalMsg public
