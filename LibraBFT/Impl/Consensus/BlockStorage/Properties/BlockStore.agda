{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap                               as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree    as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage as PersistentLivenessStorage
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

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module getBlockSpec (hv : HashValue) (bs : BlockStore) where

  Ok : Set
  Ok = ∃[ eb ] (getBlock hv bs ≡ just eb)

  postulate -- TODO-2: This contract will need to be modified when hash collisions are are modeled
    correctBlockData
      : ∀ bd → hashBD bd ≡ hv → (isOk : Ok) → let (eb , _) = isOk in
          eb ^∙ ebBlock ≈Block record (eb ^∙ ebBlock) { _bId = hv ;  _bBlockData = bd }

module executeBlockESpec (bs : BlockStore) (block : Block) where

  Ok : Set
  Ok = ∃[ eb ] (executeBlockE bs block ≡ Right eb)

  record ContractOk (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≈ : eb ^∙ ebBlock ≈Block block

  postulate -- TODO: Refine `ContractOk` and prove
    contract : (isOk : Ok) → ContractOk (proj₁ isOk)

module executeAndInsertBlockESpec (bs0 : BlockStore) (block : Block) where
  open executeAndInsertBlockE bs0 block

  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree

  Ok : Set
  Ok = ∃₂ λ bs' eb → executeAndInsertBlockE bs0 block ≡ Right (bs' , eb)

  private
    Ok' : BlockStore → ExecutedBlock → Either ErrLog (BlockStore × ExecutedBlock) → Set
    Ok' bs' eb m = m ≡ Right (bs' , eb)

  Err : Set
  Err = ∃[ e ] (executeAndInsertBlockE bs0 block ≡ Left e)

  record ContractOk (bs' : BlockStore) (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≈ : eb ^∙ ebBlock ≈Block block
      bsInv    : ∀ pre → pre ^∙ lBlockStore ≡ bs0
                 → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
      -- TODO-2: The fields below should be about blocks, not QCs. The property
      -- for QCs then follows as a consequence
      qcPost : ∀ qc → qc QCProps.∈BlockTree (bs' ^∙ bsInner)
               → qc QCProps.∈BlockTree (bs0 ^∙ bsInner) ⊎ qc ≡ block ^∙ bQuorumCert
      qcPres : ∀ pre → pre ^∙ rmBlockStore ≡ bs0
               → ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre (pre & lBlockStore ∙~ bs')

  Contract : EitherD-Post ErrLog (BlockStore × ExecutedBlock)
  Contract (Left x) = ⊤
  Contract (Right (bs' , eb)) = ContractOk bs' eb

  contract' : EitherD-weakestPre (executeAndInsertBlockE.step₀ bs0 block) Contract
  proj₂ contract' eb eb≡ =
    mkContractOk ebBlock≈ (btP bs0) (λ qc → Left) qcPres
    where
    ebBlock≈ : eb ^∙ ebBlock ≈Block block
    ebBlock≈ =
      getBlockSpec.correctBlockData (block ^∙ bId) bs0 (block ^∙ bBlockData)
        (hashBD (block ^∙ bBlockData) ≡ block ^∙ bId
         ∋ obm-dangerous-magic' "TODO: propagate this information from `Network.processProposal`")
        (eb , eb≡)

    btP : ∀ bs' pre → pre ^∙ lBlockStore ≡ bs' → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
    btP bs' pre preBS≡ = substBlockStoreInv preBS≡ refl

    qcPres : ∀ pre → pre ^∙ rmBlockStore ≡ bs0 → ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre (pre & rmBlockStore ∙~ bs0)
    qcPres pre refl qc = id

  proj₁ contract' getBlock≡nothing = contract₂
    where
    contract₂ : EitherD-weakestPre step₂ Contract
    proj₁ contract₂ _ = tt
    proj₂ contract₂ bsr bsr≡ = contract₃
      where
      contract₃ : EitherD-weakestPre (step₃ bsr) Contract
      proj₁ contract₃ _ = tt
      proj₂ contract₃ btr<br = contract₄
        where
        contract₅ : ∀ eb → eb ^∙ ebBlock ≈Block block → EitherD-weakestPre (step₅ bsr eb) Contract

        contract₄ : EitherD-weakestPre (step₄ bsr) Contract
        contract₄
           with executeBlockE bs0 block
           |    inspect (executeBlockE bs0) block
        ...| Right res | [ executeBlock≡ ] = λ where ._ refl → contract₅ res EB.ebBlock≈
           where module EB = executeBlockESpec.ContractOk (executeBlockESpec.contract bs0 block (res , executeBlock≡))
        ...| Left (ErrBlockNotFound parentBlockId) | [ executeBlockE≡ ]
           with pathFromRoot parentBlockId bs0
        ...| Left _ = tt
        ...| Right blocksToReexecute
           with (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock))
        ...| Left _ = tt
        ...| Right _
           with executeBlockE bs0 block
        ...| Left  _ = tt
        contract₄ | Left (ErrVerify _) | [ executeBlockE≡ ] = tt

        contract₅ eb eb≈
           with PersistentLivenessStorage.saveTreeE bs0 ((eb ^∙ ebBlock) ∷ []) []
        ...| Left _ = tt
        ...| Right bs1 = λ where ._ refl → contract₆
           where
           contract₆ : EitherD-weakestPre (step₆ bsr eb) Contract
           contract₆
              with insertBlockESpec.contract eb (bs0 ^∙ bsInner)
           ...| con
              with BlockTree.insertBlockE eb (bs0 ^∙ bsInner)
           ...| Left  _ = tt
           ...| Right (bt' , eb') =
             λ where ._ refl → mkContractOk ebBlock≈ btP qcPost qcPres
              where
              module IBE = insertBlockESpec.ContractOk con

              ebBlock≈ : eb' ^∙ ebBlock ≈Block block
              ebBlock≈ = sym≈Block $ begin
                block                                                  ≡⟨ sym≈Block eb≈ ⟩
                (eb  ^∙ ebBlock & bSignature ∙~ (block ^∙ bSignature)) ≡⟨ sym≈Block IBE.block≈ ⟩
                (eb' ^∙ ebBlock & bSignature ∙~ (block ^∙ bSignature)) ∎
                where open ≡-Reasoning

              btP : ∀ rm → rm ^∙ lBlockStore ≡ bs0 → Preserves BlockStoreInv rm (rm & rmBlockStore ∙~ (bs0 & bsInner ∙~ bt'))
              btP rm bs≡
                 with insertBlockESpec.preservesBlockStoreInv eb (bs0 ^∙ bsInner)
                        bt' eb' con rm (cong (_^∙ bsInner) bs≡)
              ...| Right hashCollision = ⊥-elim hashCollision -- TODO-2: propagate hash collision upward
              ...| Left pres = pres

              qcPost : QCProps.∈Post⇒∈PreOrBT (_≡ block ^∙ bQuorumCert) (bs0 ^∙ bsInner) bt'
              qcPost
                 with insertBlockESpec.qcPost eb (bs0 ^∙ bsInner)
                        bt' eb' con
              ...| qcPost' rewrite eb≈ = qcPost'

              qcPres : ∀ pre → pre ^∙ rmBlockStore ≡ bs0
                       → ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre (pre & rmBlockStore ∙~ BlockStore∙new bt' (bs0 ^∙ bsStorage))
              qcPres = obm-dangerous-magic' "TODO: refine contract for `insertBlockE`"

  contract : Contract (executeAndInsertBlockE bs0 block)
  contract = EitherD-contract (executeAndInsertBlockE.step₀ bs0 block) Contract contract'


module executeAndInsertBlockMSpec (b : Block) where
  -- NOTE: This function returns any errors, rather than producing them as output.
  module _ (pre : RoundManager) where

    bs = pre ^∙ rmBlockStore

    contract
      : ∀ Post
        → (∀ e → {- At the moment we do not need to know why it failed -} Post (Left e) pre [])
        → ((isOk : executeAndInsertBlockESpec.Ok bs b) → let (bs' , eb , _) = isOk in
             executeAndInsertBlockESpec.ContractOk bs b bs' eb
           → Post (Right eb) (pre & rmBlockStore ∙~ bs') [])
        → LBFT-weakestPre (executeAndInsertBlockM b) Post pre
    proj₁ (contract Post pfBail pfOk ._ refl) e ≡left = pfBail e
    proj₂ (contract Post pfBail pfOk ._ refl) (bs' , eb) ≡right ._ refl unit refl
       with executeAndInsertBlockESpec.contract bs b
    ...| con rewrite ≡right = pfOk (bs' , eb , refl) con

module insertSingleQuorumCertMSpec
  (qc : QuorumCert) where

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noMsgOuts     : OutputProps.NoMsgs outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        qcSigsB4      : ∀ {pool} → QCProps.QCRequirements pool qc
                        → Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre post


    postulate -- TODO-2: prove
      contract' : LBFT-weakestPre (insertSingleQuorumCertM qc) Contract pre

    contract : ∀ Q → RWST-Post-⇒ Contract Q → LBFT-weakestPre (insertSingleQuorumCertM qc) Q pre
    contract Q pf = LBFT-⇒ Contract Q pf (insertSingleQuorumCertM qc) pre contract'

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new (pre ^∙ lBlockStore ∙ bsHighestQuorumCert)
                 (pre ^∙ lBlockStore ∙ bsHighestCommitCert)
                 (pre ^∙ lBlockStore ∙ bsHighestTimeoutCert)

  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl = pf
