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
      : ∀ bd → hashBD bd ≡ hv → (isOk : Ok) → let (eb , _) = isOk in eb ^∙ ebBlock ∙ bBlockData ≡ bd

module executeBlockESpec (bs : BlockStore) (block : Block) where

  Ok : Set
  Ok = ∃[ eb ] (executeBlockE bs block ≡ Right eb)

  record ContractOk (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≡ : eb ^∙ ebBlock ≡ block

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
      ebBlockData≡ : eb ^∙ ebBlock ≡L block at bBlockData
      bsInv        : ∀ pre → pre ^∙ lBlockStore ≡ bs0
                     → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
      qcPost       : QCProps.∈Post⇒∈PreOrBT (_≡ block ^∙ bQuorumCert) (bs' ^∙ bsInner) (bs0 ^∙ bsInner)

  contract : (isOk : Ok) → let (bs' , eb , _) = isOk in ContractOk bs' eb
  contract (bs' , eb , isOk)
     with getBlock (block ^∙ bId) bs0
     |    inspect (getBlock (block ^∙ bId)) bs0
  contract (bs' , .eb , refl) | just eb | [ getbId≡ ] =
    mkContractOk ebBlockData≡ (btP bs') (λ qc → Left)
    where
    btP : ∀ bs' pre → pre ^∙ lBlockStore ≡ bs' → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')
    btP bs' pre preBS≡ = substBlockStoreInv preBS≡ refl

    ebBlockData≡ : eb ^∙ ebBlock ≡L block at bBlockData
    ebBlockData≡ =
      getBlockSpec.correctBlockData (block ^∙ bId) bs0 (block ^∙ bBlockData)
        (obm-dangerous-magic' "TODO: propagate this information from `Network.processProposal`")
        (eb , getbId≡)

  ...| nothing | [ getbId≡ ]
    with pf-step₂ isOk
    where
    pf-step₂ : Ok' bs' eb step₂ → ∃[ bsr ] (just bsr ≡ bs0 ^∙ bsRoot × Ok' bs' eb (step₃ bsr))
    pf-step₂ isOk
       with bs0 ^∙ bsRoot
    ... | just bsr = bsr , (refl , isOk)
  ...| (bsr , bsr≡ , isOk₂)
     with pf-step₃ isOk₂
     where
     pf-step₃ : Ok' bs' eb (step₃ bsr) → (block ^∙ bRound > bsr ^∙ ebRound) × Ok' bs' eb (step₄ bsr)
     pf-step₃ isOk
        with bsr ^∙ ebRound ≥?ℕ block ^∙ bRound
     ... | yes round≥ = absurd Left _ ≡ Right _ case isOk of λ ()
     ... | no  round< = ≰⇒> round< , isOk
  ...| br>bsrr , isOk₃
     with pf-step₄ isOk₃
     where
     pf-step₄ : Ok' bs' eb (step₄ bsr) → ∃[ eb' ] (eb' ^∙ ebBlock ≡L block at bBlockData × Ok' bs' eb (step₅ bsr eb'))
     pf-step₄ isOk
        with executeBlockE bs0 block
        |    inspect (executeBlockE bs0) block
     ...| Right res | [ ebe≡ ] = res , ((cong (_^∙ bBlockData) EB.ebBlock≡) , isOk)
       where
       module EB = executeBlockESpec.ContractOk (executeBlockESpec.contract bs0 block (res , ebe≡))
     ...| Left (ErrBlockNotFound parentBlockId) | [ ebe≡ ]
        with pathFromRoot parentBlockId bs0
     ...| Right blocksToReexecute
        with (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock))
     ...| Right _
        with executeBlockE bs0 block
        |    inspect (executeBlockE bs0) block
     ...| Left _ | _ = absurd Left _ ≡ Right _ case isOk of λ ()
     -- NOTE: The case below is unreachable, since we already know the result of
     -- `executeBlockE bs0 block`. This likely means the model (and Haskell
     -- prototype) needs to be updated.
     ...| Right eb' | [ ebe≡₁ ] = eb' , (cong (_^∙ bBlockData) EB.ebBlock≡) , isOk
        where
        module EB = executeBlockESpec.ContractOk (executeBlockESpec.contract bs0 block (eb' , ebe≡₁))
  ...| eb' , ebbd≡ , isOk₅
     with pf-step₅ isOk₅
     where
     pf-step₅ : Ok' bs' eb (step₅ bsr eb') → Ok' bs' eb (step₆ bsr eb')
     pf-step₅ isOk
        with PersistentLivenessStorage.saveTreeE bs0 (eb' ^∙ ebBlock ∷ []) []
     ... | Right bs1 = isOk
  ...| isOk₆ = pf-step₆ isOk₆
     where
     pf-step₆ : Ok' bs' eb (step₆ bsr eb') → ContractOk bs' eb
     pf-step₆ isOk
        with insertBlockESpec.contract eb' (bs0 ^∙ bsInner)
     ...| IBCon
        with BlockTree.insertBlockE eb' (bs0 ^∙ bsInner)
        |    inspect (BlockTree.insertBlockE eb') (bs0 ^∙ bsInner)
     pf-step₆ isOk | IBCon | Right (bt' , eb“) | [ insp ]
        with isOk
     ...| refl =
        mkContractOk ebBlockData≡ btP qcPost
        where
        module IBE = insertBlockESpec.ContractOk IBCon

        ebBlockData≡ : eb“ ^∙ ebBlock ≡L block at bBlockData
        ebBlockData≡ = begin
          eb“ ^∙ ebBlock ∙ bBlockData ≡⟨ IBE.bd≡ ⟩
          eb' ^∙ ebBlock ∙ bBlockData ≡⟨ ebbd≡ ⟩
          block ^∙ bBlockData ∎
          where open ≡-Reasoning

        btP : ∀ rm → rm ^∙ lBlockStore ≡ bs0 → Preserves BlockStoreInv rm (rm & rmBlockStore ∙~ bs')
        btP rm bs≡
          with insertBlockESpec.preservesBlockStoreInv eb' (bs0 ^∙ bsInner)
                 (bs' ^∙ bsInner) eb“ IBCon rm (cong (_^∙ bsInner) bs≡)
        ...| Right col = ⊥-elim col -- TODO: propagate hash collision upward
        ...| Left pres = pres

        qcPost : QCProps.∈Post⇒∈PreOrBT (_≡ block ^∙ bQuorumCert) bt' (bs0 ^∙ bsInner)
        qcPost
           with insertBlockESpec.qcPost eb' (bs0 ^∙ bsInner) bt' eb“ IBCon
        ...| qcPost' rewrite ebbd≡ = qcPost'

  postulate -- TODO-2: prove
    -- More properties are likely going to required in the future, as well.
    ebBlock≡ : ∀ {bs' eb} → executeAndInsertBlockE bs0 block ≡ Right (bs' , eb) → eb ^∙ ebBlock ≡ block
    bs'BlockInv
      : ∀ {bs' eb pre}
        → executeAndInsertBlockE bs0 block ≡ Right (bs' , eb)
        → bs0 ≡ pre ^∙ lBlockStore
        → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')

module executeAndInsertBlockMSpec (b : Block) where
  -- NOTE: This function returns any errors, rather than producing them as output.
  contract
    : ∀ pre Post
      → (∀ e → Left e ≡ executeAndInsertBlockE (pre ^∙ lBlockStore) b → Post (Left e) pre [])
      → (∀ bs' eb → Right (bs' , eb) ≡ executeAndInsertBlockE (pre ^∙ lBlockStore) b
         → Post (Right eb) (pre & lBlockStore ∙~ bs') [])
      → LBFT-weakestPre (executeAndInsertBlockM b) Post pre
  proj₁ (contract pre Post pfBail pfOk ._ refl) e eaibLeft = pfBail e (sym eaibLeft)
  proj₂ (contract pre Post pfBail pfOk ._ refl) (bs' , eb) eaibRight ._ refl ._ refl =
    pfOk bs' eb (sym eaibRight)

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
