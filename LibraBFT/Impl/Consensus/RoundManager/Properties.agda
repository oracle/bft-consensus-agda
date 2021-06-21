{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore       as BlockStore
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock  as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.RoundState           as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection     as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage     as PersistentLivenessStorage
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules       as SafetyRules

open RWST-do

module LibraBFT.Impl.Consensus.RoundManager.Properties where
open import LibraBFT.Impl.Consensus.RoundManager

module ExecuteAndVoteMSpec (b : Block) where
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open import LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules
  open import LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties

  record Contract (pre : RoundManager) (r : FakeErr ⊎ Vote) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noOutput       : outs ≡ []
      voteSrcCorrect : ConstructAndSignVoteM.VoteSrcCorrect pre r post

  contract : ∀ pre → RWST-weakestPre (executeAndVoteM b) (Contract pre) unit pre
  contract pre =
    ExecuteAndInsertBlockM.contract b (RWST-weakestPre-ebindPost unit (ExecuteAndVoteM.step₁ b) _) pre
      (mkContract refl unit)
      (λ where
        eb bs ._ refl cr cr≡ vs vs≡ so so≡ →
          (λ _ → mkContract refl unit)
          , λ _ → (λ _ → mkContract refl unit)
          , (λ _ →
               let maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
                   st₁                      = rmSetBlockStore pre bs in
               ConstructAndSignVoteM.contract⇒ maybeSignedVoteProposal' st₁
                 (RWST-weakestPre-ebindPost unit (ExecuteAndVoteM.step₃ b) (Contract pre))
                 (help bs)))
    where
    help : ∀ bs r st outs
           → ConstructAndSignVoteM.Contract (rmSetBlockStore pre bs) r st outs
           → _
    help bs (inj₁ _) st outs pf =
      mkContract (ConstructAndSignVoteM.Contract.noOutput pf) unit
    help bs (inj₂ vote) st outs pf ._ refl =
      SaveVoteM.contract vote (RWST-weakestPre-ebindPost unit (λ _ → ok vote) _) st
        (mkContract noo unit)
        λ where
          bs' unit _ → mkContract noo (voteSrcCorrectCod-substRm refl refl vsc)
      where
      noo = cong (_++ []) (ConstructAndSignVoteM.Contract.noOutput pf)
      vsc = ConstructAndSignVoteM.Contract.voteSrcCorrect pf

  contract⇒ : ∀ pre Post → (∀ r st outs → Contract pre r st outs → Post r st outs)
              → RWST-weakestPre (executeAndVoteM b) Post unit pre
  contract⇒ pre Post pf = RWST-impl (Contract pre) Post pf (executeAndVoteM b) unit pre (contract pre)

module ProcessProposalMSpec (proposal : Block) where
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open        LibraBFT.Impl.Consensus.RoundManager.ProcessProposalM proposal

  OutputSpec : List Output → Set
  OutputSpec outs =
    let msgs = List-filter isSendVote? outs in
    msgs ≡ [] ⊎ ∃[ sv ] (msgs ≡ sv ∷ []) -- No SendVote, or exactly one SendVote

  record Contract (pre : RoundManager) (r : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      output         : OutputSpec outs
      voteSrcCorrect : ∀ vm pid → SendVote vm pid ∈ outs → VoteSrcCorrectCod pre post (vm ^∙ vmVote)
      -- TODO-2: We will also want, likely as a separate field, that the vote is
      -- being sent to the correct peer.
      -- TODO-2: And we will want that if we return an error, we do not modify
      -- the lastVote field.

  contract : ∀ pre → RWST-weakestPre (processProposalM proposal) (Contract pre) unit pre
  contract pre ._ refl =
    IsValidProposalM.contract proposal
      (RWST-weakestPre-bindPost unit (step₁{pre} (rmGetBlockStore pre)) (Contract pre)) pre
      invalidProposal validProposal

    where
    errOuts : ∀ {st} vm pid → SendVote vm pid ∈ LogErr fakeErr ∷ [] → VoteSrcCorrectCod pre st (vm ^∙ vmVote)
    errOuts vm pid = ⊥-elim ∘ SendVote∉Output refl

    errContract : ∀ {st} → Contract pre unit st (LogErr fakeErr ∷ [])
    errContract = mkContract (inj₁ refl) errOuts

    invalidProposal : _ → _
    invalidProposal (inj₁ ≡nothing) r x₁ rewrite ≡nothing =
      (λ _ → errContract) , λ where ()
    invalidProposal (inj₂ ¬eq) r refl
       with proposal ^∙ bAuthor
    invalidProposal (inj₂ (just x)) .false refl | .(just _) =
      (λ where ()) , (λ _ → (λ _ → errContract) , λ where ())

    validProposal : Maybe-Any _ (proposal ^∙ bAuthor) → _
    validProposal any
       with proposal ^∙ bAuthor
    validProposal (just refl) | .(just _) = λ where
      ._ refl →
        (λ where ())
        , λ _ → (λ where ())
        , λ _ → (λ ≡nothing → errContract)
        , λ _ → (λ noParentOrParentRound>ProposalRound → errContract)
        , (λ _ →
           ExecuteAndVoteMSpec.contract⇒ proposal pre
             (RWST-weakestPre-bindPost unit step₂ (Contract pre))
              λ where
                (inj₁ x) st .[] (ExecuteAndVoteMSpec.mkContract refl voteSrcCorrect) ._ refl →
                  (λ where ._ refl → errContract)
                  , λ where ._ ()
                (inj₂ vote) st .[] (ExecuteAndVoteMSpec.mkContract refl voteSrcCorrect) ._ refl →
                  (λ where _ ())
                  , λ where
                     ._ refl unit _ →
                       syncInfoMSpec.contract (RWST-weakestPre-bindPost unit (step₄ vote ) (Contract pre)) st
                         λ where
                           si ._ refl ._ refl ._ refl ._ refl ._ refl →
                             mkContract
                               (inj₂ ((SendVote (VoteMsg∙new vote si) _) , refl))
                               λ where ._ ._ (here refl) → voteSrcCorrect)

module syncUpMSpec (now : Instant) (syncInfo : SyncInfo) (author : Author) (_helpRemote : Bool) where
  OutputSpec : List Output → Set
  OutputSpec outs = outs ≡ []

  StateSpec : (pre post : RoundManager) → Set
  StateSpec pre post = pre ≡L post at lSafetyData ∙ sdLastVote

  record Contract (pre : RoundManager) (r : FakeErr ⊎ Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
       outputSpec : OutputSpec outs
       postSpec   : StateSpec pre post

  -- TODO-2: Prove this, after `syncUpM` has been implemented
  postulate
    contract : ∀ pre → RWST-weakestPre (syncUpM now syncInfo author _helpRemote) (Contract pre) unit pre

  contract⇒ : ∀ pre Post → (∀ r st outs → Contract pre r st outs → Post r st outs)
              → RWST-weakestPre (syncUpM now syncInfo author _helpRemote) Post unit pre
  contract⇒ pre Post pf = RWST-impl _ _ pf (syncUpM now syncInfo author _helpRemote) unit pre (contract pre)

module ensureRoundAndSyncUpMSpec
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo) (author : Author) (helpRemote : Bool) where
  open ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote

  OutputSpec : List Output → Set
  OutputSpec outs = outs ≡ []

  StateSpec : (pre post : RoundManager) → Set
  StateSpec pre post = pre ≡L post at lSafetyData ∙ sdLastVote

  record Contract (pre : RoundManager) (r : FakeErr ⊎ Bool) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      output : OutputSpec outs
      state  : StateSpec pre post

  contract : ∀ pre
             → RWST-weakestPre
                 (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote)
                 (Contract pre) unit pre
  proj₁ (contract pre ._ refl) messageRound<currentRound = mkContract refl refl
  proj₂ (contract pre ._ refl) messageRound≥currentRound =
    syncUpMSpec.contract⇒ now syncInfo author helpRemote pre
      (RWST-weakestPre-ebindPost unit (λ _ → step₂) (Contract pre))
      (λ where
        (inj₁ x) st .[] (syncUpMSpec.mkContract refl postSpec) → mkContract refl postSpec
        (inj₂ _) st .[] (syncUpMSpec.mkContract refl postSpec) _ _ currentRound' ≡currentRound' →
          (λ _ → mkContract refl postSpec) , λ _ → mkContract refl postSpec)

module processProposalMsgMSpec (now : Instant) (pm : ProposalMsg) where


{-
module ProcessProposalM (proposal : Block) where
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  VoteSrcCorrect : RoundManager → LBFT-Post Unit
  VoteSrcCorrect pre x post outs =
    ∀ vm αs → SendVote vm αs ∈ outs → VoteSrcCorrectCod pre post (vm ^∙ mvmVote)

  c₁ : ErrLog ⊎ Vote → LBFT Unit
  c₁ _r =
    caseM⊎ (_r) of λ where
      (inj₁ _) → pure unit
      (inj₂ vote) → do
        RoundState.recordVote (unmetaVote vote)
        si ← BlockStore.syncInfo
        recipient ← ProposerElection.getValidProposer
                      <$> use lProposerElection
                      <*> pure (proposal ^∙ bRound + 1)
        act (SendVote (VoteMsgWithMeta∙fromVote vote si) (recipient ∷ []))

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
    proj₂ (impl ._ st .[] (refl , pf) .(inj₂ _) refl) (Vote∙new vote mvsNew) refl unit _ =
      GetSyncInfo.contract _ st λ where
        _ r _ _ _ _ _ _ _ _ _ _ _ .(VoteMsgWithMeta∙new (VoteMsg∙new vote r) mvsNew) .(_ ∷ []) (here refl) →
          pf
    proj₂ (impl ._ st .[] (refl , pf) .(inj₂ _) refl) (Vote∙new vote mvsLastVote) refl unit _ =
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
    ∀ vm αs → SendVote vm αs ∈ outs → VoteSrcCorrectCod pre post (vm ^∙ mvmVote)

  Contract : RoundManager → LBFT-Post Unit
  Contract pre x post outs =
    ∀ m → m ∈ outs →
    ∃₂ λ vm αs → m ≡ SendVote vm αs × VoteSrcCorrectCod pre post (vm ^∙ mvmVote)

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
-}
