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
open import LibraBFT.ImplShared.Interface.Output
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
    let msgs = List-filter isOutputMsg? outs in
    msgs ≡ [] ⊎ ∃₂ λ vm pid → (msgs ≡ SendVote vm (pid ∷ []) ∷ []) -- No SendVote, or exactly one SendVote

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
               (inj₁ _) st .[] (ExecuteAndVoteMSpec.mkContract refl voteSrcCorrect) ._ refl →
                 mkContract (inj₁ refl) (λ where vm pid (here ()))
               (inj₂ vote) st .[] (ExecuteAndVoteMSpec.mkContract refl voteSrcCorrect) ._ refl ._ refl →
                 syncInfoMSpec.contract (RWST-weakestPre-bindPost unit (step₃ vote) (Contract pre)) st
                   (λ where
                     si ._ refl ._ refl ._ refl ._ refl ._ refl →
                       mkContract (Right (_ , _ , refl)) λ where vm pid (here refl) → voteSrcCorrect))

module syncUpMSpec (now : Instant) (syncInfo : SyncInfo) (author : Author) (_helpRemote : Bool) where
  OutputSpec : List Output → Set
  OutputSpec outs = outs ≡ []

  StateSpec : (pre post : RoundManager) → Set
  StateSpec pre post = pre ≡L post at₁ lSafetyData ∙ sdLastVote

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
  StateSpec pre post = pre ≡L post at₁ lSafetyData ∙ sdLastVote

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

  contract⇒ : ∀ pre Post
              → (∀ r st outs → Contract pre r st outs → Post r st outs)
              → RWST-weakestPre
                  (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote)
                  Post unit pre
  contract⇒ pre Post pf = RWST-impl _ Post pf step₀ unit pre (contract pre)


module processProposalMsgMSpec (now : Instant) (pm : ProposalMsg) where

  record Contract-HasOuts
    (pre : RoundManager) (_ : Unit) (post : RoundManager) (msgs : List Output)
    (vm : VoteMsg) (pid : NodeId) : Set where
    constructor mkContract-HasOuts
    field
      msgs≡    : msgs ≡ SendVote vm (pid ∷ []) ∷ []
      ep≡      : pm ≡L vm at (pmProposal ∙ bBlockData ∙ bdEpoch , vmVote ∙ vEpoch)
      lvr-pre  : pre ^∙ lSafetyData ∙ sdLastVotedRound < vm ^∙ vmVote ∙ vRound
                 ⊎ just (vm ^∙ vmVote) ≡ (pre ^∙ lSafetyData ∙ sdLastVote)
      lvr-post : just (vm ^∙ vmVote) ≡ (post ^∙ lSafetyData ∙ sdLastVote)

  Contract : (pre : RoundManager) (r : Unit) (post : RoundManager) (outs : List Output) → Set
  Contract pre r post outs =
    let msgs = List-filter isOutputMsg? outs in
    msgs ≡ [] ⊎ ∃₂ λ vm pid → Contract-HasOuts pre r post msgs vm pid

  -- TODO-1: Prove this
  postulate
    contract : ∀ pre → RWST-weakestPre (processProposalMsgM now pm) (Contract pre) unit pre

  contract⇒ : ∀ pre Post → (∀ r st outs → Contract pre r st outs → Post r st outs)
              → RWST-weakestPre (processProposalMsgM now pm) Post unit pre
  contract⇒ pre Post pf = RWST-impl (Contract pre) Post pf (processProposalMsgM now pm) unit pre (contract pre)
