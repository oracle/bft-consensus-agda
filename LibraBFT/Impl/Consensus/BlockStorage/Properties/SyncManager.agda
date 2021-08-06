{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.Impl.Consensus.BlockStorage.SyncManager
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.SyncManager where

module addCertsMSpec
  (syncInfo : SyncInfo) (retriever : BlockRetriever) where

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcSigsB4  : QCProps.SyncInfoRequirements pool syncInfo
                    → Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre post

    postulate
      contract' : LBFT-weakestPre (addCertsM syncInfo retriever) Contract pre

    contract : ∀ Q → RWST-Post-⇒ Contract Q → LBFT-weakestPre (addCertsM syncInfo retriever) Q pre
    contract Q pf = LBFT-⇒ Contract Q pf (addCertsM syncInfo retriever) pre contract'


module insertQuorumCertMSpec
  (qc : QuorumCert) (retriever : BlockRetriever) where

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- outQcs∈RMor   : QCProps.OutputQc∈RmOr outs pre post (_≡ qc)
