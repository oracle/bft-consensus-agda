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

  postulate -- TODO-2: Refine contract
            -- This contract is only a sketch, and will need to be modified when
            -- hash collisions are are modeled.
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

  ------   These are used only outside this module.  
  Ok : Set
  Ok = ∃₂ λ bs' eb → executeAndInsertBlockE bs0 block ≡ Right (bs' , eb)

  private
    Ok' : BlockStore → ExecutedBlock → Either ErrLog (BlockStore × ExecutedBlock) → Set
    Ok' bs' eb m = m ≡ Right (bs' , eb)

  Err : Set
  Err = ∃[ e ] (executeAndInsertBlockE bs0 block ≡ Left e)
  ------

  record ContractOk (bs' : BlockStore) (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≈ : hashBD (block ^∙ bBlockData) ≡ block ^∙ bId → eb ^∙ ebBlock ≈Block block
      bsInv    : ∀ pre → pre ^∙ lBlockStore ≡ bs0
                 → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
      -- executeAndInsertBlockE does not modify BlockTree fields other than btIDToBlock
      bs≡x : bs0 ≡ (bs' & (bsInner ∙ btIdToBlock) ∙~ (bs0 ^∙ bsInner ∙ btIdToBlock))

  Contract : EitherD-Post ErrLog (BlockStore × ExecutedBlock)
  Contract (Left x) = ⊤
  Contract (Right (bs' , eb)) = ContractOk bs' eb

  contract' : EitherD-weakestPre step₀ Contract
  proj₂ contract' eb eb≡ =
    mkContractOk ebBlock≈ (btP bs0) refl
    where
    ebBlock≈ : hashBD (block ^∙ bBlockData) ≡ block ^∙ bId → eb ^∙ ebBlock ≈Block block
    ebBlock≈ bid≡ =
      getBlockSpec.correctBlockData
        (block ^∙ bId) bs0 (block ^∙ bBlockData) (bid≡) (eb , eb≡)

    btP : ∀ bs' pre → pre ^∙ lBlockStore ≡ bs' → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
    btP bs' pre preBS≡ = substBlockStoreInv preBS≡ refl

    qcPres : ∀ qc → PreservesL (qc QCProps.∈RoundManager_) rmBlockStore bs0 bs0
    qcPres qc rm = id

  proj₁ contract' getBlock≡nothing = contract₁
    where
    contract₁ : EitherD-weakestPre step₁ Contract
    proj₁ contract₁ _ = tt
    proj₁ (proj₂ contract₁ bsr bsr≡) _ = tt
    proj₂ (proj₂ contract₁ bsr bsr≡) btr<br = contract₂
      where
      contract₃ : ∀ eb → ExecutedBlock∙new block stateComputeResult ≡ eb
                  → EitherD-weakestPre (step₃ eb) Contract

      contract₂ : EitherD-weakestPre (step₂ bsr) Contract
      proj₂ contract₂ eb eb≡ ._ refl =
        contract₃ eb (inj₂-injective eb≡)
      proj₁ contract₂ (ErrCBlockNotFound _) executeBlockE≡Left = tt
      proj₁ contract₂ (ErrVerify _) executeBlockE≡Left = tt
      -- > eitherSD (pathFromRoot parentBlockId bs0) LeftD λ blocksToReexecute →
      proj₁ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) _ _ = tt
      -- > case⊎D (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
      proj₁ (proj₂ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) blocksToReexecute btr≡) _ _ = tt
      proj₂ (proj₂ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) blocksToReexecute btr≡) _ _ eb eb≡ =
        contract₃ eb (sym eb≡)

      contract₃ eb eb≡ bs1 bs1≡ = contract₄
        where
        contract₄ : EitherD-weakestPre (step₄ eb) Contract
        contract₄
           with insertBlockESpec.contract eb (bs0 ^∙ bsInner)
        ...| con
           with BlockTree.insertBlockE.E eb (bs0 ^∙ bsInner)
        ...| Left _ = tt
        ...| Right (bt' , eb') =
           λ where ._ refl → mkContractOk (const ebBlock≈) btP bss≡x
           where
           module IBE = insertBlockESpec.ContractOk con

           eb≈ : block ≡ eb ^∙ ebBlock
           eb≈ = cong (_^∙ ebBlock) eb≡

           ebBlock≈ : eb' ^∙ ebBlock ≈Block block
           ebBlock≈ = sym≈Block $ begin
             block
               ≡⟨ eb≈ ⟩
             (eb  ^∙ ebBlock)
               ≡⟨ cong (λ b → eb ^∙ ebBlock & bSignature ∙~ (b ^∙ bSignature)) (sym eb≈) ⟩
             (eb  ^∙ ebBlock & bSignature ∙~ (block ^∙ bSignature))
               ≡⟨ sym≈Block IBE.block≈ ⟩
             (eb' ^∙ ebBlock & bSignature ∙~ (block ^∙ bSignature))
               ∎
             where open ≡-Reasoning

           bts≡x : _
           bts≡x = IBE.bt≡x

           btP : ∀ rm → rm ^∙ lBlockStore ≡ bs0 → Preserves BlockStoreInv rm (rm & rmBlockStore ∙~ (bs0 & bsInner ∙~ bt'))
           btP rm preBS≡ = substBlockStoreInv-qcMap (trans (cong (_^∙ bsInner ∙ btIdToQuorumCert) preBS≡)
                                                           (cong _btIdToQuorumCert bts≡x)) refl

           bss≡x : bs0 ≡ (bs0 & bsInner ∙~ bt' & bsInner ∙ btIdToBlock ∙~ (bs0 ^∙ (bsInner ∙ btIdToBlock)))
           bss≡x rewrite sym bts≡x = refl

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
        qcPost : QCProps.∈Post⇒∈PreOr (_≡ qc) pre post

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
