{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
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
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.RoundManager.Properties where

module executeAndVoteMSpec (b : Block) where

  open executeAndVoteM b
  open SafetyRulesProps

  epoch = b ^∙ bEpoch
  round = b ^∙ bRound

  ResultCorrect : (pre post : RoundManager) (r : Either ErrLog Vote) → Set
  ResultCorrect pre post (Left e) = NoVoteCorrect pre post ⊎ VoteNotSaved pre post epoch round
  ResultCorrect pre post (Right v) = VoteCorrect pre post epoch round v

  record Contract (pre : RoundManager) (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noOuts        : NoMsgOuts outs
      inv           : NoEpochChange pre post
      resultCorrect : ResultCorrect pre post r

  contract'
    : ∀ pre
      → LBFT-weakestPre (executeAndVoteM b) (Contract pre) pre
  proj₁ (contract' pre ._ refl) err isErr ._ refl =
    mkContract refl (mkNoEpochChange refl refl) (inj₁ (mkNoVoteCorrect refl ≤-refl))
  proj₁ (proj₂ (contract' pre ._ refl) (bs' , eb) isOk ._ refl ._ refl .eb refl cr cr≡ vs vs≡ so so≡) _ =
    mkContract refl (mkNoEpochChange refl refl) (inj₁ (mkNoVoteCorrect refl ≤-refl))
  proj₁ (proj₂ (proj₂ (contract' pre ._ refl) (bs' , eb) isOk ._ refl ._ refl .eb refl cr cr≡ vs vs≡ so so≡) _) _ =
    mkContract refl (mkNoEpochChange refl refl) (inj₁ (mkNoVoteCorrect refl ≤-refl))
  proj₂ (proj₂ (proj₂ (contract' pre ._ refl) (bs' , eb) isOk ._ refl ._ refl .eb refl cr cr≡ vs vs≡ so so≡) _) _ =
    constructAndSignVoteMSpec.contract maybeSignedVoteProposal' preUpdated
      (RWST-weakestPre-ebindPost unit step₃ (Contract pre))
      pf
    where
    maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb
    preUpdated = rmSetBlockStore pre bs'

    constructAndSignVoteMSpec-Contract =
      constructAndSignVoteMSpec.Contract preUpdated
        (constructAndSignVoteMSpec.epoch maybeSignedVoteProposal')
        (constructAndSignVoteMSpec.round maybeSignedVoteProposal')

    noEpochChange-pre-preUpdated : NoEpochChange pre preUpdated
    noEpochChange-pre-preUpdated = mkNoEpochChange refl refl

    eb≡b = (BlockStoreProps.executeAndInsertBlockESpec.ebBlock≡ (rmGetBlockStore pre) b isOk)

    eb≡b-epoch : (eb ^∙ ebBlock) ≡L b at bEpoch
    eb≡b-epoch rewrite eb≡b = refl

    eb≡b-round : (eb ^∙ ebBlock) ≡L b at bRound
    eb≡b-round rewrite eb≡b = refl

    pf : ∀ r st outs → constructAndSignVoteMSpec-Contract r st outs → RWST-weakestPre-ebindPost unit step₃ (Contract pre) r st outs
    pf (Left _) st outs (constructAndSignVoteMSpec.mkContract noOuts (mkNoEpochChange es≡₁ es≡₂) (mkNoVoteCorrect lv≡ lvr≤)) =
      mkContract noOuts (mkNoEpochChange es≡₁ es≡₂) (inj₁ (mkNoVoteCorrect lv≡ lvr≤))
    pf (Right vote) st outs (constructAndSignVoteMSpec.mkContract noOuts nec vc) ._ refl =
      PersistentLivenessStorageProps.saveVoteMSpec.contract vote
        (RWST-weakestPre-ebindPost unit (λ _ → ok vote) Contract-++outs) st
        (mkContract
          (++-NoMsgOuts outs [] noOuts refl)
          (transNoEpochChange noEpochChange-pre-preUpdated nec)
          (Right voteNotSaved))
        λ where
          _ .unit refl →
            mkContract (++-NoMsgOuts outs [] noOuts refl)
              (transNoEpochChange (noEpochChange-pre-preUpdated) (transNoEpochChange nec (mkNoEpochChange refl refl)))
              voteSaved
      where
      Contract-++outs = RWST-Post++ (Contract pre) outs

      voteNotSaved : VoteNotSaved pre st epoch round
      voteNotSaved = vote , substVoteCorrect refl refl refl refl eb≡b-epoch eb≡b-round vc

      voteSaved : ∀ {bs} → VoteCorrect pre (rmSetBlockStore st bs) epoch round vote
      voteSaved = substVoteCorrect refl refl refl refl eb≡b-epoch eb≡b-round vc

  contract
    : ∀ pre Post
      → (∀ r st outs → Contract pre r st outs → Post r st outs)
      → LBFT-weakestPre (executeAndVoteM b) Post pre
  contract pre Post pf =
    RWST-⇒ (Contract pre) Post pf (executeAndVoteM b) unit pre (contract' pre)
