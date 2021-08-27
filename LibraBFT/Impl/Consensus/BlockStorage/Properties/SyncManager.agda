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
open import LibraBFT.Impl.OBM.Logging.Logging
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

open Invariants
open RoundManagerTransProps
open OutputProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.SyncManager where

module insertQuorumCertMSpec
  (qc : QuorumCert) (retriever : BlockRetriever) where

  open insertQuorumCertM qc retriever
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost  : QCProps.∈Post⇒∈PreOr (_≡ qc) pre post

  private -- NOTE: need to re-generalize over `pre` because the prestate might differ
    module step₁Spec (bs : BlockStore) (pool : SentMessages) (pre : RoundManager) where
      postulate -- TODO-2: Prove
        contract' : LBFT-weakestPre (step₁ bs) (Contract pre) pre

      contract : ∀ Q → RWST-Post-⇒ (Contract pre) Q → LBFT-weakestPre (step₁ bs) Q pre
      contract Q pf = LBFT-⇒ (Contract pre) Q pf (step₁ bs) pre contract'


  module _ (pool : SentMessages) (pre : RoundManager) where
    contract' : LBFT-weakestPre (insertQuorumCertM qc retriever) (Contract pre) pre
    proj₁ (contract' bs@._ refl) _ nfIsLeft ._ refl = step₁Spec.contract' bs pool pre
    proj₂ (contract' bs@._ refl) NeedFetch nf≡ =
      obm-dangerous-magic' "TODO: waiting on contract for `fetchQuorumCertM`"
    proj₂ (contract' bs@._ refl) QCBlockExist nf≡ =
      insertSingleQuorumCertMSpec.contract qc pre Post₁ contract₁
      where
      Post₁ : LBFT-Post (Either ErrLog Unit)
      Post₁ =
        (RWST-weakestPre-∙^∙Post unit (withErrCtx $ "" ∷ [])
          (RWST-weakestPre-ebindPost unit (λ _ → use lBlockStore >>= (λ _ → logInfo fakeInfo) >> ok unit)
            (RWST-weakestPre-bindPost unit (λ _ → step₁ bs) (Contract pre))))

      module _ (r₁ : Either ErrLog Unit) (st₁ : RoundManager) (outs₁ : List Output) (con₁ : insertSingleQuorumCertMSpec.Contract qc pre r₁ st₁ outs₁) where
        module ISQC = insertSingleQuorumCertMSpec.Contract con₁

        contract₁' : ∀ outs' → NoMsgs outs' → RWST-Post-⇒ (Contract st₁) (RWST-Post++ (Contract pre) outs')
        contract₁' outs' noMsgs r₂ st₂ outs₂ con₂ =
          mkContract
            (transPreservesRoundManagerInv ISQC.rmInv Step₁.rmInv)
            (transNoEpochChange{i = pre}{st₁}{st₂} ISQC.noEpochChange Step₁.noEpochChange)
            (++-NoVotes outs' outs₂ (NoMsgs⇒NoVotes outs' noMsgs) Step₁.noVoteOuts)
            (transVoteNotGenerated ISQC.noVote Step₁.noVote)
            (QCProps.++-OutputQc∈RoundManager{st₂}{outs'}{outs₂} (QCProps.NoMsgs⇒OutputQc∈RoundManager outs' st₂ noMsgs) Step₁.outQcs∈RM)
            qcPost
          where
          module Step₁ = Contract con₂

          qcPost : QCProps.∈Post⇒∈PreOr (_≡ qc) pre st₂
          qcPost qc qc∈st₂
             with Step₁.qcPost qc qc∈st₂
          ...| Right qc≡ = Right qc≡
          ...| Left qc∈st₁
             with ISQC.qcPost qc qc∈st₁
          ...| Right qc≡ = Right qc≡
          ...| Left qc∈pre = Left qc∈pre

      contract₁ : RWST-Post-⇒ (insertSingleQuorumCertMSpec.Contract qc pre) Post₁
      contract₁ (Left _) st₁ outs₁ con₁ ._ refl ._ refl =
        step₁Spec.contract bs pool st₁ (RWST-Post++ (Contract pre) (outs₁ ++ []))
          (contract₁' _ _ _ con₁ (outs₁ ++ [])
            (++-NoMsgs outs₁ [] (insertSingleQuorumCertMSpec.Contract.noMsgOuts con₁) refl))
      contract₁ (Right y) st₁ outs₁ con₁ ._ refl ._ refl ._ refl ._ refl ._ refl =
        step₁Spec.contract bs pool st₁ (RWST-Post++ (Contract pre) ((outs₁ ++ []) ++ LogInfo fakeInfo ∷ []))
          (contract₁' _ _ _ con₁ ((outs₁ ++ []) ++ LogInfo fakeInfo ∷ [])
            (++-NoMsgs (outs₁ ++ []) (LogInfo fakeInfo ∷ [])
              (++-NoMsgs outs₁ [] (insertSingleQuorumCertMSpec.Contract.noMsgOuts con₁) refl)
              refl))

    proj₂ (contract' bs@._ refl) QCRoundBeforeRoot _ ._ refl = step₁Spec.contract' bs pool pre
    proj₂ (contract' bs@._ refl) QCAlreadyExist _ ._ refl = step₁Spec.contract' bs pool pre

module addCertsMSpec
  (syncInfo : SyncInfo) (retriever : BlockRetriever) where

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
        -- Signatures
        noOutQc : QCProps.¬OutputQc outs
        qcPost  : QCProps.∈Post⇒∈PreOr (_QC∈SyncInfo syncInfo) pre post

    postulate -- TODO-2: prove
      contract' : LBFT-weakestPre (addCertsM syncInfo retriever) Contract pre

    contract : ∀ Q → RWST-Post-⇒ Contract Q → LBFT-weakestPre (addCertsM syncInfo retriever) Q pre
    contract Q pf = LBFT-⇒ Contract Q pf (addCertsM syncInfo retriever) pre contract'
