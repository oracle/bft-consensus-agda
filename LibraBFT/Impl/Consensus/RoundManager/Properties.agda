{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore            as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore as BlockStoreProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock       as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.RoundState                as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection          as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage          as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties as PersistentLivenessStorageProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules            as SafetyRules
import      LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules as SafetyRulesProps
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

module LibraBFT.Impl.Consensus.RoundManager.Properties where

module executeAndVoteMSpec (b : Block) where

  open executeAndVoteM b
  open SafetyRulesProps
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  epoch = b ^∙ bEpoch
  round = b ^∙ bRound

  ResultCorrect : (pre post : RoundManager) (strict : Bool) (r : Either ErrLog Vote) → Set
  ResultCorrect pre post strict (Left e) = NoVoteCorrect pre post strict ⊎ VoteNotSaved pre post epoch round
  ResultCorrect pre post _ (Right v) = VoteCorrect pre post epoch round v

  record Contract (pre : RoundManager) (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noOuts        : NoMsgOuts outs
      inv           : NoEpochChange pre post
      lvr≡?    : Bool
      resultCorrect : ResultCorrect pre post lvr≡? r

  contract'
    : ∀ pre
      → LBFT-weakestPre (executeAndVoteM b) (Contract pre) pre
  contract' pre =
    executeAndInsertBlockMSpec.contract b pre
      (RWST-weakestPre-∙^∙Post unit withErrCtxt (RWST-weakestPre-ebindPost unit step₁ (Contract pre)))
        (λ where e e≡ ._ refl → contractBail [] refl)
        contract-step₁
    where
    contractBail : ∀ {e} outs → NoMsgOuts outs → Contract pre (Left e) pre outs
    contractBail outs noMsgOuts = mkContract noMsgOuts reflNoEpochChange true (Left reflNoVoteCorrect)

    module _
      (bs' : BlockStore) (eb : ExecutedBlock)
      (eaibRight : Right (bs' , eb) ≡ BlockStore.executeAndInsertBlockE (pre ^∙ lBlockStore) b) where

      preUpdateBS = pre & lBlockStore ∙~ bs'

      eb≡b = (BlockStoreProps.executeAndInsertBlockESpec.ebBlock≡ (pre ^∙ lBlockStore) b (sym eaibRight))

      eb≡b-epoch : (eb ^∙ ebBlock) ≡L b at bEpoch
      eb≡b-epoch rewrite eb≡b = refl

      eb≡b-round : (eb ^∙ ebBlock) ≡L b at bRound
      eb≡b-round rewrite eb≡b = refl

      contractBailSetBS : ∀ {e} outs → NoMsgOuts outs → Contract pre (Left e) preUpdateBS outs
      contractBailSetBS outs noMsgOuts = mkContract noMsgOuts (mkNoEpochChange refl refl) true (Left (mkNoVoteCorrect refl refl))

      contract-step₁
        : RWST-weakestPre-∙^∙Post unit withErrCtxt
            (RWST-weakestPre-ebindPost unit step₁ (Contract pre)) (Right eb) preUpdateBS []
      contract-step₂
        : RWST-weakestPre (step₂ eb) (Contract pre) unit preUpdateBS

      proj₁ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡just = contractBailSetBS [] refl
      proj₁ (proj₂ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡none) so≡true = contractBailSetBS [] refl
      proj₂ (proj₂ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡none) so≡false = contract-step₂

      maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb

      contract-step₂ =
        constructAndSignVoteMSpec.contract maybeSignedVoteProposal' preUpdateBS
          (RWST-weakestPre-ebindPost unit step₃ (Contract pre)) pf
        where
        pf : RWST-Post-⇒
               (constructAndSignVoteMSpec.Contract preUpdateBS _ _)
               (RWST-weakestPre-ebindPost unit step₃ (Contract pre))
        pf (Left x) st outs (constructAndSignVoteMSpec.mkContract noOuts inv lvr≡? resultCorrect) =
          mkContract noOuts
            (transNoEpochChange (mkNoEpochChange refl refl) inv)
            lvr≡?
            (Left (transNoVoteCorrect (mkNoVoteCorrect refl refl) resultCorrect))
        pf (Right vote) st outs (constructAndSignVoteMSpec.mkContract noOuts inv lvr≡? resultCorrect) ._ refl =
          PersistentLivenessStorageProps.saveVoteMSpec.contract vote
            (RWST-weakestPre-ebindPost unit (const (ok vote)) (RWST-Post++ (Contract pre) outs)) st
            (λ outs₁ noMsgOuts noErrOuts →
              mkContract (++-NoMsgOuts outs outs₁ noOuts noMsgOuts)
                (transNoEpochChange (mkNoEpochChange refl refl) inv)
                false (Right
                        (pseudotransVoteNotSaved{s₂ = preUpdateBS}
                          (mkNoVoteCorrect refl refl)
                          (vote , convRC resultCorrect))))
            λ where
              outs₁ noMsgOuts noErrOuts ._ refl →
                mkContract
                  (++-NoMsgOuts outs (outs₁ ++ []) noOuts (++-NoMsgOuts outs₁ [] noMsgOuts refl))
                  (transNoEpochChange (mkNoEpochChange refl refl) inv)
                  false (pseudotransVoteCorrect (mkNoVoteCorrect refl refl) (convRC resultCorrect))
          where
          convRC : _ → VoteCorrect preUpdateBS st (b ^∙ bEpoch) (b ^∙ bRound) _
          convRC rc rewrite sym eb≡b-epoch | sym eb≡b-round = rc

  contract
    : ∀ pre Post
      → (∀ r st outs → Contract pre r st outs → Post r st outs)
      → LBFT-weakestPre (executeAndVoteM b) Post pre
  contract pre Post pf =
    RWST-⇒ (Contract pre) Post pf (executeAndVoteM b) unit pre (contract' pre)

module processProposalMSpec (proposal : Block) where
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open        LibraBFT.Impl.Consensus.RoundManager.processProposalM proposal

  epoch = proposal ^∙ bEpoch
  round = proposal ^∙ bRound

  record Contract (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noEpochChage    : NoEpochChange pre post
      noBroadcastOuts : NoBroadcastOuts outs
      nv⊎vmoc         : NoVote⊎VoteMsgOutsCorrect pre post outs epoch round

  contract' : ∀ pre → LBFT-weakestPre (processProposalM proposal) (Contract pre) pre
  contract' pre ._ refl =
    isValidProposalMSpec.contract proposal pre
      (RWST-weakestPre-bindPost unit (step₁ (pre ^∙ lBlockStore)) (Contract pre))
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
    contractBail : ∀ {outs} → NoMsgOuts outs → Contract pre unit pre outs
    contractBail{outs} nmo =
      mkContract
        reflNoEpochChange
        (NoMsgOuts⇒NoBroadcastOuts{outs} nmo)
        (Left (true , mkNoVoteMsgOutsCorrect (NoMsgOuts⇒NoVoteOuts{outs} nmo) (Left reflNoVoteCorrect)))

    contract-step₂ : RWST-weakestPre (executeAndVoteM proposal >>= step₂) (Contract pre) unit pre
    contract-step₂ =
      executeAndVoteMSpec.contract proposal pre
        (RWST-weakestPre-bindPost unit step₂ (Contract pre)) pf
      where
      pf : RWST-Post-⇒ (executeAndVoteMSpec.Contract proposal pre) (RWST-weakestPre-bindPost unit step₂ (Contract pre))
      pf (Left x) st outs (executeAndVoteMSpec.mkContract noOuts inv lvr≡? resultCorrect) ._ refl =
        mkContract inv
          (++-NoMsgOuts-NoBroadcastOuts outs (LogErr fakeErr ∷ []) noOuts refl)
          (Left (lvr≡? , mkNoVoteMsgOutsCorrect (++-NoMsgOuts-NoVoteOuts outs _ noOuts refl) resultCorrect))
      pf (Right vote) st outs (executeAndVoteMSpec.mkContract noOuts inv lvr≡? resultCorrect) ._ refl ._ refl ._ refl =
        syncInfoMSpec.contract (st & rsVoteSent-rm ∙~ just vote)
          (RWST-weakestPre-bindPost unit (step₃ vote) (RWST-Post++ (Contract pre) outs))
          λ si si≡ → contract-step₃ si
        where
        module _ (si : SyncInfo) where
          contract-step₃ : RWST-weakestPre (step₃ vote si) (RWST-Post++ (Contract pre) outs) unit (st & rsVoteSent-rm ∙~ just vote)
          contract-step₃ ._ refl ._ refl ._ refl ._ refl recipient@._ refl =
            mkContract
              (transNoEpochChange inv (mkNoEpochChange refl refl))
              (++-NoMsgOuts-NoBroadcastOuts outs _ noOuts refl)
              (Right (mkVoteMsgOutsCorrect
                       (VoteMsg∙new vote si) recipient
                       (++-NoMsgOuts-VoteMsgOuts outs _ ((VoteMsg∙new vote si)) (recipient ∷ []) noOuts refl)
                       (substVoteCorrect refl refl refl refl refl refl resultCorrect)))

  contract : ∀ pre Post → RWST-Post-⇒ (Contract pre) Post → LBFT-weakestPre (processProposalM proposal) Post pre
  contract pre Post pf = LBFT-⇒ (Contract pre) Post pf (processProposalM proposal) pre (contract' pre)

module syncUpM
  (now : Instant) (syncInfo : SyncInfo) (author : Author) (_helpRemote : Bool) where

  record Contract (pre : RoundManager) (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noEpochChange : NoEpochChange pre post
      noVoteOuts    : NoVoteOuts outs
      noVote        : NoVoteCorrect pre post true

  postulate
    contract' : ∀ pre → LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) (Contract pre) pre

  contract
    : ∀ pre Post → (∀ r st outs → Contract pre r st outs → Post r st outs)
      → LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Post pre
  contract pre Post pf =
    LBFT-⇒ (Contract pre) Post pf (syncUpM now syncInfo author _helpRemote) pre
      (contract' pre)

module ensureRoundAndSyncUpMSpec
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo)
  (author : Author) (helpRemote : Bool) where

  open ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote

  record Contract (pre : RoundManager) (r : Either ErrLog Bool) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noEpochChange : NoEpochChange pre post
      noVoteOuts    : NoVoteOuts outs
      noVote        : NoVoteCorrect pre post true

  postulate
    contract'
      : ∀ pre → LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) (Contract pre) pre

  contract : ∀ pre Post → RWST-Post-⇒ (Contract pre) Post → LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Post pre
  contract pre Post pf =
    LBFT-⇒ (Contract pre) Post pf (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) pre (contract' pre)

module processProposalMsgMSpec
  (now : Instant) (pm : ProposalMsg) where

  open processProposalMsgM now pm

  epoch = pm ^∙ pmProposal ∙ bEpoch
  round = pm ^∙ pmProposal ∙ bRound

  record Contract (pre : RoundManager) (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noEpochChange : NoEpochChange pre post
      outsCorrect   : NoVote⊎VoteMsgOutsCorrect pre post outs epoch round

  contract' : ∀ pre → LBFT-weakestPre (processProposalMsgM now pm) (Contract pre) pre
  contract' pre rewrite processProposalMsgM≡ = contract
    where
    contractBail : ∀ outs → NoVoteOuts outs → Contract pre unit pre outs
    contractBail outs nvo =
      mkContract reflNoEpochChange (Left (true , (mkNoVoteMsgOutsCorrect nvo (Left reflNoVoteCorrect))))

    contract : LBFT-weakestPre step₀ (Contract pre) pre
    proj₁ contract ≡nothing = contractBail _ refl
    proj₂ contract = contract-step₁
      where
      module _ (pAuthor : Author) (pAuthor≡ : pm ^∙ pmProposer ≡ just pAuthor) where
        step₂-pf : RWST-Post-⇒ _ (RWST-weakestPre-bindPost unit step₂ (Contract pre))

        contract-step₁ : LBFT-weakestPre (step₁ pAuthor) (Contract pre) pre
        contract-step₁ =
          ensureRoundAndSyncUpMSpec.contract now round (pm ^∙ pmSyncInfo) pAuthor true pre
            (RWST-weakestPre-bindPost unit step₂ (Contract pre)) step₂-pf

        step₂-pf (Left      e) st outs (ensureRoundAndSyncUpMSpec.mkContract noEpochChange noVoteOuts noVote) ._ refl =
          mkContract noEpochChange (Left (true , (mkNoVoteMsgOutsCorrect (++-NoVoteOuts outs _ noVoteOuts refl) (Left noVote))))
        step₂-pf (Right false) st outs (ensureRoundAndSyncUpMSpec.mkContract noEpochChange noVoteOuts noVote) ._ refl ._ refl =
          mkContract noEpochChange (Left (true , (mkNoVoteMsgOutsCorrect (++-NoVoteOuts outs _ noVoteOuts refl) (Left noVote))))
        step₂-pf (Right  true) st outs (ensureRoundAndSyncUpMSpec.mkContract noEpochChange noVoteOuts noVote) ._ refl =
          processProposalMSpec.contract (pm ^∙ pmProposal) st (RWST-Post++ (Contract pre) outs) step₃-pf
          where
          step₃-pf : RWST-Post-⇒ _ (RWST-Post++ (Contract pre) outs)
          step₃-pf r' st' outs' (processProposalMSpec.mkContract noEpochChange' noBroadcastOuts' (Left (strict? , nvmoc))) =
            mkContract (transNoEpochChange noEpochChange noEpochChange') (Left (strict? , pseudotransNoVoteMsgOutsCorrect noVoteOuts noVote nvmoc))
          step₃-pf r' st' outs' (processProposalMSpec.mkContract noEpochChange' noBroadcastOuts' (Right vmoc@(mkVoteMsgOutsCorrect vm pid voteMsgOuts voteCorrect))) =
            mkContract ((transNoEpochChange noEpochChange noEpochChange'))
              (Right (mkVoteMsgOutsCorrect vm pid (++-NoVoteOuts-VoteMsgOuts outs _ vm (pid ∷ []) noVoteOuts voteMsgOuts)
              (pseudotransVoteCorrect noVote voteCorrect)))

  contract : ∀ pre Post → RWST-Post-⇒ (Contract pre) Post → LBFT-weakestPre (processProposalMsgM now pm) Post pre
  contract pre Post pf =
    LBFT-⇒ (Contract pre) Post pf (processProposalMsgM now pm) pre (contract' pre)
