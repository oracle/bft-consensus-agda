{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Prelude
open import Optics.All

open RoundManagerInvariants
open QCProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree where


module insertBlockESpec (block : ExecutedBlock) (bt : BlockTree) where

  record ContractOk (bt“ : BlockTree) (b : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      bd≡ : b ≡L block at (ebBlock ∙ bBlockData)
      -- TODO-1: the returned block tree is the same as the previous block tree at all values not equal to b ^∙ ebId

  Contract : Either ErrLog (BlockTree × ExecutedBlock) → Set
  Contract (Left _) = ⊤
  Contract (Right (bt' , b)) = ContractOk bt' b

  postulate -- TODO-1: prove, (waiting on: refinement of `ContractOk`)
    contract : Contract (insertBlockE block bt)

  module _ (bt“ : BlockTree) (b : ExecutedBlock) (con : ContractOk bt“ b) where

    postulate -- TODO-1: prove (waiting on: refinement of assumption)
      preservesBlockStoreInv
        : ∀ rm → rm ^∙ rmBlockStore ∙ bsInner ≡ bt
          → Preserves BlockStoreInv rm (rm & rmBlockStore ∙ bsInner ∙~ bt“)
            ⊎ ⊥ -- NOTE: This disjunct is for when there is a hash collision
                -- between b ^∙ ebBlock ∙ bBlockData and block ^∙ ebBlock ∙
                -- bBlockdata

      qcPost : ∀ qc → qc QCProps.∈BlockTree bt“ → qc QCProps.∈BlockTree bt ⊎ qc ≡ block ^∙ ebBlock ∙ bQuorumCert


module insertQuorumCertESpec
  (qc : QuorumCert) (bt0  : BlockTree) where

  Contract : Either ErrLog (BlockTree × List InfoLog) → Set
  Contract (Left _) = Unit
  Contract (Right (bt1 , il)) = ∀ {qc'} → qc' ∈BlockTree bt1 → qc' ∈BlockTree bt0 ⊎ qc' ≡ qc

  postulate -- TODO-1: prove it
    contract : Contract (insertQuorumCertE qc bt0)
