{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.EpochManager
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore            as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore as BlockStoreProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock       as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.RoundState                as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection          as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage          as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties as PersistentLivenessStorageProps
open import LibraBFT.Impl.Consensus.RoundManager
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules            as SafetyRules
import      LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules as SafetyRulesProps
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open OutputProps
open Invariants
open RoundManagerTransProps

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

module LibraBFT.Impl.Consensus.RoundManager.Properties where

module executeAndVoteMSpec (vb : ValidBlock) where
  b = vbBlock vb

  open executeAndVoteM b
  open SafetyRulesProps
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  isbQc = (_≡ b ^∙ bQuorumCert)

  VoteResultCorrect : (pre post : RoundManager) (lvr≡? : Bool) (r : Either ErrLog Vote) → Set
  VoteResultCorrect pre post lvr≡? (Left _) =
    VoteNotGenerated pre post lvr≡? ⊎ Voting.VoteGeneratedUnsavedCorrect pre post b
  VoteResultCorrect pre post lvr≡? (Right vote) =
    Voting.VoteGeneratedCorrect pre post vote b

  module _ (pre : RoundManager) where

    open QCProps
    open Invariants.Reqs b (pre ^∙ lBlockTree)

    record Contract (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General properties / invariants
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noMsgOuts     : OutputProps.NoMsgs outs
        -- Voting
        lvr≡?             : Bool
        voteResultCorrect : NoHC1 → VoteResultCorrect pre post lvr≡? r
        -- QCs
        qcPost : ∈Post⇒∈PreOr isbQc pre post

    contract' :
      LBFT-weakestPre (executeAndVoteM b) Contract pre
    contract' =
      executeAndInsertBlockMSpec.contract vb pre Post₀
        (λ where e ._ refl → contractBail [] refl)
        contract₁
      where
      Post₀ : LBFT-Post (Either ErrLog ExecutedBlock)
      Post₀ = RWS-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ []))
                (RWS-weakestPre-ebindPost unit step₁ Contract)

      contractBail : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) pre outs
      contractBail{e} outs noMsgOuts =
        mkContract
          reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          noMsgOuts true (const vrc)
          qcPost
        where
        vrc : VoteResultCorrect pre pre true (Left e)
        vrc = inj₁ reflVoteNotGenerated

        qcPost : ∈Post⇒∈PreOr isbQc pre pre
        qcPost qc = Left

      module EAIBM = executeAndInsertBlockMSpec vb
      module EAIBE = executeAndInsertBlockESpec (EAIBM.bs pre) vb
      module _ (isOk : EAIBE.Ok) (con : EAIBE.ContractOk (proj₁ isOk) (proj₁ (proj₂ isOk))) where

        module EAIBECon = EAIBE.ContractOk con

        bs' = proj₁ isOk
        eb  = proj₁ (proj₂ isOk)

        pre₁ = pre & rmBlockStore ∙~ bs'

        -- State invariants
        module _  where
          bsP : Preserves BlockStoreInv (rm→BlockStore-EC pre) (rm→BlockStore-EC pre₁)
          bsP bsi = EAIBECon.bsInv bsi

          srP : Preserves SafetyRulesInv (pre ^∙ lSafetyRules) (pre₁ ^∙ lSafetyRules)
          srP = mkPreservesSafetyRulesInv id

        invP₁ : Preserves RoundManagerInv pre pre₁
        invP₁ = mkPreservesRoundManagerInv id id bsP srP

        qcPost-BT : _
        qcPost-BT = ∈Post⇒∈PreOrBT-QCs≡ isbQc
                                        (cong (_^∙ bsInner ∙ btHighestCommitCert) EAIBECon.bs≡x)
                                        (cong (_^∙ bsInner ∙ btHighestQuorumCert) EAIBECon.bs≡x)

        qcPost₁ : ∈Post⇒∈PreOr isbQc pre pre₁
        qcPost₁ = ∈Post⇒∈PreOr-∙-BT-RM isbQc pre pre₁ qcPost-BT

        -- For the case any of the checks in `step₁` fails
        contractBail₁ : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) pre₁ outs
        contractBail₁ outs noMsgOuts =
          mkContract invP₁ refl
            noMsgOuts true (const $ inj₁ (mkVoteNotGenerated refl refl))
            qcPost₁

        contract₁ : Post₀ (Right eb) pre₁ []
        proj₁ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _ = contractBail₁ [] refl
        proj₁ (proj₂ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _) _ = contractBail₁ [] refl
        proj₂ (proj₂ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _) _ = contract₂
          where
          maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb

          module CASV = constructAndSignVoteMSpec

          proposedBlock = CASV.proposedBlock maybeSignedVoteProposal'

          Post₂ : LBFT-Post (Either ErrLog Vote)
          Post₂ = RWS-weakestPre-ebindPost unit step₃ Contract

          contract₂ : RWS-weakestPre (step₂ eb) Contract unit pre₁

          contract₂⇒ : RWS-Post-⇒ (CASV.Contract pre₁ proposedBlock) Post₂
          contract₂⇒ r pre₃ outs con = contract₂⇒-help r CASVCon.voteResCorrect
            where
            module CASVCon = CASV.Contract con
            CASVouts = outs

            invP₂ = transPreservesRoundManagerInv invP₁ CASVCon.rmInv

            qcPost₂ : QCProps.∈Post⇒∈PreOr (_≡ b ^∙ bQuorumCert) pre pre₃
            qcPost₂ = obm-dangerous-magic' "TODO: waiting on `constructAndSignVoteM` contract"

            contract₂⇒-help :
              (r : Either ErrLog Vote) (vrc : CASV.VoteResultCorrect pre₁ pre₃ proposedBlock CASVCon.lvr≡? r)
              → RWS-weakestPre-ebindPost unit step₃ Contract r pre₃ outs
            contract₂⇒-help (Left _) vrc =
              mkContract invP₂ CASVCon.noEpochChange CASVCon.noMsgOuts
                CASVCon.lvr≡? (const ∘ Left $ (transVoteNotGenerated (mkVoteNotGenerated refl refl) vrc))
                qcPost₂
            contract₂⇒-help (Right vote) vrc ._ refl = contract₃
              where

              open RoundManagerInv
              open BlockStoreInv
              open BlockTreeInv

              contract₃ : RWS-weakestPre (step₃ vote) (RWS-Post++ Contract CASVouts) unit pre₃
              contract₃ =
                PersistentLivenessStorageProps.saveVoteMSpec.contract vote
                  Post₃ pre₃
                  contractBail₃ contractOk₃
                where
                Post₃ : LBFT-Post (Either ErrLog Unit)
                Post₃ = RWS-weakestPre-ebindPost unit (const $ ok vote) (RWS-Post++ Contract CASVouts)

                vgc₃ : NoHC1 → Voting.VoteGeneratedCorrect pre pre₃ vote b {- proposedBlock -}
                vgc₃ nohc =
                  Voting.glue-VoteNotGenerated-VoteGeneratedCorrect
                    (mkVoteNotGenerated refl refl)
                    (Voting.substVoteGeneratedCorrect proposedBlock b
                      (EAIBECon.ebBlock≈ nohc)
                      vrc)

                noMsgOutsBail₃ : ∀ outs → NoMsgs outs → NoMsgs (CASVouts ++ outs)
                noMsgOutsBail₃ outs noMsgs = ++-NoMsgs CASVouts outs CASVCon.noMsgOuts noMsgs

                noMsgOutsOk₃ : ∀ outs → NoMsgs outs → NoMsgs (CASVouts ++ outs ++ [])
                noMsgOutsOk₃ outs noMsgs rewrite ++-identityʳ outs = noMsgOutsBail₃ outs noMsgs

                contractBail₃ : ∀ outs → NoMsgs outs → NoErrors outs → Post₃ (Left fakeErr) pre₃ outs
                contractBail₃ outs noMsgOuts noErrOuts =
                  mkContract invP₂ CASVCon.noEpochChange (noMsgOutsBail₃ outs noMsgOuts)
                    CASVCon.lvr≡? ((Right ∘ Voting.mkVoteGeneratedUnsavedCorrect vote) ∘ vgc₃)
                    qcPost₂

                contractOk₃ : ∀ outs → NoMsgs outs → NoErrors outs → Post₃ (Right unit) pre₃ outs
                contractOk₃ outs noMsgs noErrs unit refl =
                  mkContract invP₂ CASVCon.noEpochChange (noMsgOutsOk₃ outs noMsgs)
                    CASVCon.lvr≡? vgc₃ qcPost₂

          contract₂ = constructAndSignVoteMSpec.contract maybeSignedVoteProposal' pre₁ Post₂ contract₂⇒

    contract
      : ∀ Post
        → RWS-Post-⇒ Contract Post
        → LBFT-weakestPre (executeAndVoteM b) Post pre
    contract Post pf =
      RWS-⇒ (executeAndVoteM b) unit pre contract' pf

module processProposalMSpec (vproposal : ValidBlock) where
  proposal = vbBlock vproposal

  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open        LibraBFT.Impl.Consensus.RoundManager.processProposalM proposal

  module _ (pre : RoundManager) where

    open Invariants.Reqs (vbBlock vproposal) (pre ^∙ lBlockTree)

    record Contract (u : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
         -- General properties / invariants
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noProposals   : OutputProps.NoProposals outs
        -- Voting
        voteAttemptCorrect : NoHC1 → Voting.VoteAttemptCorrect pre post outs proposal
        -- QCs
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost    : QCProps.∈Post⇒∈PreOr (_≡ proposal ^∙ bQuorumCert) pre post

    contract' : LBFT-weakestPre (processProposalM proposal) Contract pre
    contract' ._ refl =
      isValidProposalMSpec.contract proposal pre
        (RWS-weakestPre-bindPost unit (step₁ (pre ^∙ lBlockStore)) Contract)
        (λ where
          mAuthor≡nothing ._ refl → (λ _ → contractBail refl) , (λ where ()))
        (λ where
          notValid ._ refl → (λ _ → contractBail refl) , (λ where ()))
        λ where
          vp ._ refl →
            (λ where ())
            , (λ _ →
                 (λ _ → contractBail refl)
                 , (λ _ →
                      (λ _ → contractBail refl)
                      , (λ _ → contract-step₂)))
      where
      contractBail : ∀ {outs} → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail{outs} nmo =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          noProposals vac outQcs qcPost
        where
          noProposals : NoProposals outs
          noProposals = OutputProps.NoMsgs⇒NoProposals outs nmo

          vac : NoHC1 → Voting.VoteAttemptCorrect pre pre outs proposal
          vac _ = Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo)

          outQcs : QCProps.OutputQc∈RoundManager outs pre
          outQcs = QCProps.NoMsgs⇒OutputQc∈RoundManager outs pre nmo

          qcPost : QCProps.∈Post⇒∈PreOr _ pre pre
          qcPost qc = Left

      contract-step₂ : RWS-weakestPre (executeAndVoteM proposal >>= step₂) Contract unit pre
      contract-step₂ =
        executeAndVoteMSpec.contract vproposal pre
          (RWS-weakestPre-bindPost unit step₂ Contract) pf-step₂
        where
        module EAV = executeAndVoteMSpec vproposal

        pf-step₂ : RWS-Post-⇒ (EAV.Contract pre) (RWS-weakestPre-bindPost unit step₂ Contract)
        pf-step₂ r st outs con = pf r EAVSpec.voteResultCorrect
          where
          module EAVSpec = executeAndVoteMSpec.Contract con
          rmInv₂ = transPreservesRoundManagerInv reflPreservesRoundManagerInv EAVSpec.rmInv

          pf : (r : Either ErrLog Vote) (vrc : NoHC1 → EAV.VoteResultCorrect pre st EAVSpec.lvr≡? r)
               → RWS-weakestPre-bindPost unit step₂ Contract r st outs
          pf (Left _) vrc ._ refl =
            mkContract rmInv₂ EAVSpec.noEpochChange
              noProposals
              vac
              qcOuts EAVSpec.qcPost
            where
            noMsgs : NoMsgs (outs ++ LogErr _ ∷ [])
            noMsgs = ++-NoMsgs outs (LogErr _ ∷ []) EAVSpec.noMsgOuts refl

            noProposals : NoProposals (outs ++ LogErr _ ∷ [])
            noProposals = NoMsgs⇒NoProposals (outs ++ LogErr _ ∷ []) noMsgs

            vac : NoHC1 → Voting.VoteAttemptCorrect pre st (outs ++ LogErr _ ∷ []) proposal
            vac nohc =
              inj₁ (EAVSpec.lvr≡?
                   , Voting.mkVoteUnsentCorrect
                       (NoMsgs⇒NoVotes (outs ++ LogErr _ ∷ []) noMsgs) (vrc nohc))

            qcOuts : QCProps.OutputQc∈RoundManager (outs ++ LogErr _ ∷ []) st
            qcOuts = QCProps.NoMsgs⇒OutputQc∈RoundManager (outs ++ LogErr _ ∷ []) st noMsgs

          pf (Right vote) vrc ._ refl ._ refl ._ refl =
            syncInfoMSpec.contract (st & rsVoteSent-rm ?~ vote)
              (RWS-weakestPre-bindPost unit (step₃ vote) (RWS-Post++ Contract outs))
              contract-step₃
            where
            stUpdateRS = st & rsVoteSent-rm ?~ vote

            module _
              (si : SyncInfo)
              (si≡ : si ≡ SyncInfo∙new
                            (st ^∙ lBlockStore ∙ bsHighestQuorumCert)
                            (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                            (st ^∙ lBlockStore ∙ bsHighestTimeoutCert))
              where
              contract-step₃ : RWS-weakestPre (step₃ vote si) (RWS-Post++ Contract outs) unit stUpdateRS
              contract-step₃ ._ refl ._ refl ._ refl ._ refl recipient@._ refl =
                mkContract rmInv₃
                  (transNoEpochChange{i = pre}{j = st}{k = stUpdateRS} EAVSpec.noEpochChange refl)
                  (OutputProps.++-NoProposals outs _ (OutputProps.NoMsgs⇒NoProposals outs EAVSpec.noMsgOuts) refl)
                  vac
                  outQcs qcPost
                where
                vm = VoteMsg∙new vote si

                vac : NoHC1 → Voting.VoteAttemptCorrect pre stUpdateRS (outs ++ SendVote vm _ ∷ []) proposal
                vac nohc =
                  inj₂ (Voting.mkVoteSentCorrect vm recipient
                         (OutputProps.++-NoVotes-OneVote outs _ (OutputProps.NoMsgs⇒NoVotes outs EAVSpec.noMsgOuts) refl)
                         (Voting.glue-VoteGeneratedCorrect-VoteNotGenerated{s₂ = st}
                           (vrc nohc) (mkVoteNotGenerated refl refl)))

                outQcs : QCProps.OutputQc∈RoundManager (outs ++ SendVote vm _ ∷ []) stUpdateRS
                outQcs =
                  QCProps.++-OutputQc∈RoundManager{stUpdateRS}{outs}
                    (QCProps.NoMsgs⇒OutputQc∈RoundManager outs stUpdateRS EAVSpec.noMsgOuts)
                    (outQcSendVote ∷ [])
                  where
                  outQcSendVote : ∀ qc nm → qc QC∈NM nm → nm Msg∈Out (SendVote vm _) → qc QCProps.∈RoundManager stUpdateRS
                  outQcSendVote qc .(V (VoteMsg∙new vote si)) (inSI inV (withVoteSIHighQC qc≡)) inSV rewrite si≡ =
                    QCProps.inHQC (sym qc≡)
                  outQcSendVote qc .(V (VoteMsg∙new vote si)) (inSI inV (withVoteSIHighCC qc≡)) inSV =
                    QCProps.inHCC (just-injective $
                      begin
                        just qc ≡⟨ lem₁ ⟩
                        sixxx   ≡⟨ lem₂ (cong is-just (sym lem₁)) ⟩
                        just (stUpdateRS ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert) ∎)
                    where
                    open ≡-Reasoning
                    sixxx = if (st ^∙ lBlockStore ∙ bsHighestQuorumCert) QCBoolEq (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                            then nothing
                            else (just $ (st ^∙ lBlockStore ∙ bsHighestCommitCert))

                    lem₁ : just qc ≡ sixxx
                    lem₁ = begin
                      just qc ≡⟨ sym qc≡ ⟩
                      vm ^∙ vmSyncInfo ∙ sixxxHighestCommitCert ≡⟨ cong (_^∙ sixxxHighestCommitCert) si≡ ⟩
                      sixxx ∎

                    lem₂ : is-just sixxx ≡ true
                           → sixxx ≡ just (stUpdateRS ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert)
                    lem₂ isj
                        with (st ^∙ lBlockStore ∙ bsHighestQuorumCert) QCBoolEq (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                    ... | false = refl
                    ... | true = absurd false ≡ true case isj of λ ()

                qcPost : QCProps.∈Post⇒∈PreOr (_≡ proposal ^∙ bQuorumCert) pre stUpdateRS
                qcPost qc qc∈stUpdateRS = EAVSpec.qcPost qc (qc∈st qc∈stUpdateRS)
                  where
                  qc∈st : qc QCProps.∈RoundManager stUpdateRS → qc QCProps.∈RoundManager st
                  qc∈st (QCProps.inHQC qc≡) = QCProps.inHQC qc≡
                  qc∈st (QCProps.inHCC qc≡) = QCProps.inHCC qc≡

                -- state invariants
                module _ where
                  bsP : Preserves BlockStoreInv (rm→BlockStore-EC st) (rm→BlockStore-EC stUpdateRS)
                  bsP = id

                  srP : Preserves SafetyRulesInv (st ^∙ lSafetyRules) (stUpdateRS ^∙ lSafetyRules)
                  srP = mkPreservesSafetyRulesInv id

                  rmInv₃ : Preserves RoundManagerInv pre stUpdateRS
                  rmInv₃ = transPreservesRoundManagerInv rmInv₂
                           (mkPreservesRoundManagerInv id id bsP srP)

    contract : ∀ Post → RWS-Post-⇒ Contract Post → LBFT-weakestPre (processProposalM proposal) Post pre
    contract Post pf = LBFT-⇒ (processProposalM proposal) pre contract' pf

module syncUpMSpec
  (now : Instant) (syncInfo : SyncInfo) (author : Author) (_helpRemote : Bool) where

  open syncUpM now syncInfo author _helpRemote
  open import LibraBFT.Impl.Consensus.ConsensusTypes.Properties.SyncInfo
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.SyncManager

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        dnmBtIdToBlk  : post ≡L pre at (lBlockTree ∙ btIdToBlock)
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- QCs
        noOutQcs : QCProps.¬OutputQc outs
        qcPost    : QCProps.∈Post⇒∈PreOr (_QC∈SyncInfo syncInfo) pre post

    contract' : LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Contract pre
    contract' =
      BlockStoreProps.syncInfoMSpec.contract pre
        (RWS-weakestPre-bindPost unit step₁ Contract)
        contract₁
      where
      localSyncInfo = BlockStoreProps.syncInfoMSpec.syncInfo pre

      contract₁ : RWS-weakestPre-bindPost unit step₁ Contract (BlockStoreProps.syncInfoMSpec.syncInfo pre) pre []
      proj₂ (contract₁ localSyncInfo lsi≡) hnc≡false =
        mkContract reflPreservesRoundManagerInv refl (reflNoEpochChange{pre}) refl
          (reflVoteNotGenerated{pre})
          [] qcPost
        where
        outQcs : QCProps.OutputQc∈RoundManager [] pre
        outQcs = QCProps.NoMsgs⇒OutputQc∈RoundManager [] pre refl

        qcPost : QCProps.∈Post⇒∈PreOr _ pre pre
        qcPost qc = Left
      proj₁ (contract₁ localSyncInfo lsi≡) hcn≡true vv@._ refl =
        verifyMSpec.contract syncInfo vv pre Post₁
          contract₃
        where
        Post₁ : LBFT-Post (Either ErrLog Unit)
        Post₁ = (RWS-weakestPre-∙^∙Post unit (withErrCtx (here' []))
                  (RWS-weakestPre-ebindPost unit (λ _ → step₃ localSyncInfo vv) Contract))

        contract₃ : RWS-Post-⇒ (verifyMSpec.Contract syncInfo vv pre) Post₁
        contract₃ r st outs con ._ refl
           with VSpec.noStateChange
           where module VSpec = verifyMSpec.Contract con
        contract₃ (Left x) st outs con ._ refl
           | refl
           = mkContract VSpec.rmInv (cong (_^∙ lBlockTree ∙ btIdToBlock) VSpec.noStateChange) (reflNoEpochChange{st})
               (++-NoVotes outs [] (NoMsgs⇒NoVotes outs VSpec.noMsgOuts) refl)
               (reflVoteNotGenerated{st})
               noOutQcs qcPost
           where
           module VSpec = verifyMSpec.Contract con
           noOutQcs : QCProps.¬OutputQc (outs ++ [])
           noOutQcs = QCProps.++-¬OutputQc (QCProps.NoMsgs⇒¬OutputQc outs VSpec.noMsgOuts) []

           qcPost : QCProps.∈Post⇒∈PreOr _ st st
           qcPost qc = Left
        contract₃ (Right y) st₃ outs₃ con₃ ._ refl
           | refl = λ where
             unit refl →
               addCertsMSpec.contract syncInfo retriever st₃
                 Post₃ contract₄
           where
           Post₃ : LBFT-Post (Either ErrLog Unit)
           Post₃ = (RWS-weakestPre-∙^∙Post unit (withErrCtx (here' []))
                     (RWS-weakestPre-ebindPost unit (λ _ → step₄ localSyncInfo vv)
                       (RWS-Post++ Contract (outs₃ ++ []))))

           retriever = BlockRetriever∙new now author

           contract₄ : RWS-Post-⇒ (addCertsMSpec.Contract syncInfo retriever st₃) Post₃
           contract₄ (Left  _) st₄ outs₄ con₄ ._ refl =
             mkContract AC.rmInv AC.dnmBtIdToBlk AC.noEpochChange noVotes₄ AC.noVote noOutQcs AC.qcPost
             where
             module AC    = addCertsMSpec.Contract con₄
             module VSpec = verifyMSpec.Contract con₃

             noVotes₄ : NoVotes $ (outs₃ ++ []) ++ outs₄ ++ []
             noVotes₄ =
               ++-NoVotes (outs₃ ++ []) (outs₄ ++ [])
                 (++-NoVotes outs₃ [] (NoMsgs⇒NoVotes outs₃ VSpec.noMsgOuts) refl)
                 (++-NoVotes outs₄ [] AC.noVoteOuts refl)

             noOutQcs : QCProps.¬OutputQc ((outs₃ ++ []) ++ outs₄ ++ [])
             noOutQcs =
               QCProps.++-¬OutputQc
                 (QCProps.++-¬OutputQc
                   (QCProps.NoMsgs⇒¬OutputQc outs₃ VSpec.noMsgOuts)
                   (QCProps.NoMsgs⇒¬OutputQc [] refl))
                 (QCProps.++-¬OutputQc
                   AC.noOutQc (QCProps.NoMsgs⇒¬OutputQc [] refl))

           contract₄ (Right _) st₄ outs₄ con₄ ._ refl =
             obm-dangerous-magic' "TODO: waiting on contract for `processCertificatesM`"

    contract
      : ∀ Post → RWS-Post-⇒ Contract Post
        → LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Post pre
    contract Post pf =
      LBFT-⇒ (syncUpM now syncInfo author _helpRemote) pre
        contract' pf

module ensureRoundAndSyncUpMSpec
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo)
  (author : Author) (helpRemote : Bool) where

  open ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Bool) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        dnmBtIdToBlk  : post ≡L pre at (lBlockTree ∙ btIdToBlock)
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        noOutQcs : QCProps.¬OutputQc outs
        qcPost   : QCProps.∈Post⇒∈PreOr (_QC∈SyncInfo syncInfo) pre post

    contract'
      : LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Contract pre
    proj₁ (contract' ._ refl) _         =
      mkContract id refl refl refl vng outqcs qcPost
      where
        vng : VoteNotGenerated pre pre true
        vng = mkVoteNotGenerated refl refl

        outqcs : QCProps.¬OutputQc []
        outqcs = []

        qcPost : QCProps.∈Post⇒∈PreOr _ pre pre
        qcPost qc = Left

    proj₂ (contract' ._ refl) mrnd≥crnd = contract-step₁
      where
      contract-step₁ : LBFT-weakestPre step₁ Contract pre
      contract-step₁ = syncUpMSpec.contract now syncInfo author helpRemote pre Post contract-step₁'
        where
        Post = RWS-weakestPre-ebindPost unit (const step₂) Contract

        contract-step₁' : _
        contract-step₁' (Left  _   ) st outs con =
          mkContract SU.rmInv SU.dnmBtIdToBlk SU.noEpochChange SU.noVoteOuts SU.noVote SU.noOutQcs SU.qcPost
          where
          module SU = syncUpMSpec.Contract con
        contract-step₁' (Right unit) st outs con = contract-step₂
          where
          module SU = syncUpMSpec.Contract con

          noVoteOuts' : NoVotes (outs ++ [])
          noVoteOuts' = ++-NoVotes outs [] SU.noVoteOuts refl

          noOutQcs : QCProps.¬OutputQc (outs ++ [])
          noOutQcs =
            QCProps.++-¬OutputQc SU.noOutQcs []

          contract-step₂ : Post (Right unit) st outs
          proj₁ (contract-step₂ ._ refl ._ refl) _ =
            mkContract SU.rmInv SU.dnmBtIdToBlk SU.noEpochChange noVoteOuts' SU.noVote
              noOutQcs SU.qcPost
          proj₂ (contract-step₂ ._ refl ._ refl) _ =
            mkContract SU.rmInv SU.dnmBtIdToBlk SU.noEpochChange noVoteOuts' SU.noVote
              noOutQcs SU.qcPost

    contract : ∀ Post → RWS-Post-⇒ Contract Post → LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Post pre
    contract Post pf =
      LBFT-⇒ (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) pre contract' pf

module processProposalMsgMSpec
  (now : Instant) (pm : ProposalMsg) (vproposal : BlockId-correct (pm ^∙ pmProposal)) where

  proposal = pm ^∙ pmProposal
  open processProposalMsgM now pm

  module _ (pre : RoundManager) where

    open Invariants.Reqs proposal (pre ^∙ lBlockTree)

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        -- Voting
        voteAttemptCorrect : NoHC1 → Voting.VoteAttemptCorrect pre post outs proposal
        -- QCs
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost    : QCProps.∈Post⇒∈PreOr (_QC∈NM (P pm)) pre post

    contract' : LBFT-weakestPre (processProposalMsgM now pm) Contract pre
    contract' rewrite processProposalMsgM≡ = contract
      where
      contractBail : ∀ outs → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail outs nmo =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre}) vac outqcs qcPost
        where
        vac : NoHC1 → Voting.VoteAttemptCorrect pre pre outs proposal
        vac _ = Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo)

        outqcs : QCProps.OutputQc∈RoundManager outs pre
        outqcs = QCProps.NoMsgs⇒OutputQc∈RoundManager outs pre nmo

        qcPost : QCProps.∈Post⇒∈PreOr _ pre pre
        qcPost qc = Left

      contract : LBFT-weakestPre step₀ Contract pre
      proj₁ contract ≡nothing = contractBail _ refl
      proj₂ contract = contract-step₁
        where
        -- These arguments come from the second proof obligation of RWS-weakestPre for RWS-maybe
        module _ (pAuthor : Author) (pAuthor≡ : pm ^∙ pmProposer ≡ just pAuthor) where
          pf-step₂ : RWS-Post-⇒ _ (RWS-weakestPre-bindPost unit step₂ Contract)

          contract-step₁ : LBFT-weakestPre (step₁ pAuthor) Contract pre
          contract-step₁ =
            ensureRoundAndSyncUpMSpec.contract now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo) pAuthor true pre
            (RWS-weakestPre-bindPost unit step₂ Contract)
            pf-step₂

          pf-step₂ r st outs con = pf-step₂' r
            where
            module ERASU = ensureRoundAndSyncUpMSpec.Contract con
            contractBailAfterSync : ∀ outs' → OutputProps.NoMsgs outs' → RWS-Post++ Contract outs unit st outs'
            contractBailAfterSync outs' noMsgs' =
              mkContract ERASU.rmInv ERASU.noEpochChange vac outqcs qcPost
              where
              vac : NoHC1 → Voting.VoteAttemptCorrect pre st (outs ++ outs') proposal
              vac _ = Left (true , (Voting.mkVoteUnsentCorrect
                                     (OutputProps.++-NoVotes outs _ ERASU.noVoteOuts (OutputProps.NoMsgs⇒NoVotes outs' noMsgs'))
                                     (Left ERASU.noVote)))

              outqcs : QCProps.OutputQc∈RoundManager (outs ++ outs') st
              outqcs =
                QCProps.¬OutputQc⇒OutputQc∈RoundManager (outs ++ outs') st
                  (QCProps.++-¬OutputQc ERASU.noOutQcs
                    (QCProps.NoMsgs⇒¬OutputQc outs' noMsgs'))

              qcPost : QCProps.∈Post⇒∈PreOr (_QC∈NM (P pm)) pre st
              qcPost qc qc∈st
                 with ERASU.qcPost qc qc∈st
              ... | Left qc∈pre = Left qc∈pre
              ... | Right qc∈si = Right (inSI inP qc∈si)

            pf-step₂' : (r : Either ErrLog Bool) → RWS-weakestPre-bindPost unit step₂ Contract r st outs
            pf-step₂' (Left e) ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right false) ._ refl ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right true) ._ refl =
              processProposalMSpec.contract (proposal , vproposal)
                                            st
                                            (RWS-Post++ Contract outs)
                                            pf-step₃
              where

              pf-step₃ : RWS-Post-⇒
                           (processProposalMSpec.Contract (proposal , vproposal) _)
                           (RWS-Post++ Contract outs)
              pf-step₃ unit st' outs' con =
                mkContract
                  (transPreservesRoundManagerInv ERASU.rmInv (PP.rmInv con))
                  (transNoEpochChange{i = pre}{j = st}{k = st'} ERASU.noEpochChange (PP.noEpochChange con))
                  vac outqcs qcPost
                where
                module PP = processProposalMSpec.Contract
                vac : NoHC1 → Voting.VoteAttemptCorrect pre st' (outs ++ outs') proposal
                vac nohc rewrite sym ERASU.dnmBtIdToBlk =
                  Voting.glue-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs}
                    ERASU.noVote ERASU.noVoteOuts (PP.voteAttemptCorrect con nohc)

                outqcs : QCProps.OutputQc∈RoundManager (outs ++ outs') st'
                outqcs =
                  QCProps.++-OutputQc∈RoundManager {rm = st'}
                    (QCProps.¬OutputQc⇒OutputQc∈RoundManager outs st' ERASU.noOutQcs)
                    (PP.outQcs∈RM con)

                qcPost : QCProps.∈Post⇒∈PreOr (_QC∈NM (P pm)) pre st'
                qcPost qc qc∈st'
                   with PP.qcPost con qc qc∈st'
                ...| Right refl = Right inP
                ...| Left qc∈st
                   with ERASU.qcPost qc qc∈st
                ... | Right qc∈si = Right (inSI inP qc∈si)
                ... | Left qc∈pre = Left qc∈pre

    contract : ∀ Post → RWS-Post-⇒ Contract Post → LBFT-weakestPre (processProposalMsgM now pm) Post pre
    contract Post pf =
      LBFT-⇒ (processProposalMsgM now pm) pre contract' pf


module startSpec
  (now          : Instant)
  (lastVoteSent : Maybe Vote)
  where

  module _ (pre : RoundManager)
           (rmi : RoundManagerInv pre) -- preconditions needed to prove contract
    where

    open InitProofDefs

    open start now lastVoteSent

    Contract : LBFT-Post Unit
    Contract _ post outs = ∃[ e ] (find' LogErrMB outs ≡ just e)
                         ⊎ find' LogErrMB outs ≡ nothing × InitContractOk post outs

    syncInfo = SyncInfo∙new (pre ^∙ (lBlockStore ∙ bsHighestQuorumCert))
                            (pre ^∙ (lBlockStore ∙ bsHighestCommitCert))
                            (pre ^∙ (lBlockStore ∙ bsHighestTimeoutCert))

    postulate
      contract-step₁ : LBFT-weakestPre (step₁-abs syncInfo) Contract pre

    contract' : LBFT-weakestPre (start-abs now lastVoteSent) Contract pre
              -- These are due to the various binds arising from syncInfoM, which is not abstract
              -- because it's more trouble than it's worth
    contract' rewrite start-abs-≡ =
      λ where ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl si refl → contract-step₁
