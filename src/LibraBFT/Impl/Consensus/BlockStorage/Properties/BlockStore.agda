{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree    as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.StateComputerByteString   as SCBS
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.ByteString
open import Util.Hash
open import Util.KVMap                                        as Map
open import Util.PKCS
open import Util.Prelude
open import Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

open Invariants
open RoundManagerTransProps
open QCProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module new
  (storage              : PersistentLivenessStorage)
  (initialData          : RecoveryData)
  (stateComp            : StateComputer)
  (maxPrunedBlocksInMem : Usize)
  where

  -- TODO-2: May require refinement (additional requirements and/or properties, particularly regarding ECinfo)
  Contract : ECinfo → EitherD-Post ErrLog BlockStore
  Contract _ (Left _)   = ⊤
  Contract eci (Right bs) = BlockStoreInv (bs , eci)

  postulate
    contract : ∀ {eci}
             → Contract eci (new-e-abs storage initialData stateComp maxPrunedBlocksInMem)

module executeBlockESpec (bs : BlockStore) (block : Block) where

  record ContractOk (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≡ : block ≡ eb ^∙ ebBlock

  Contract : EitherD-Post ErrLog _
  Contract (Left _)  = Unit
  Contract (Right y) = ContractOk y

  contract : EitherD-weakestPre (executeBlockE bs block) Contract
  contract rewrite executeBlockE≡
     with SCBS.compute (bs ^∙ bsStateComputer) block (block ^∙ bParentId)
  ...| Left _  = unit
  ...| Right _ = mkContractOk refl

  contract' : ∀ PP → (EitherD-Post-⇒ Contract PP) → EitherD-weakestPre (executeBlockE bs block) PP
  contract' PP impl = EitherD-⇒ (executeBlockE bs block) contract impl

module executeAndInsertBlockESpec (bs0 : BlockStore) (vblock : ValidBlock) where
  block   = vbBlock vblock
  block-c = vbValid vblock
  open executeAndInsertBlockE bs0 block

  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree

  blockId = block ^∙ bId

  ------   These are used only outside this module.  
  Ok : Set
  Ok = ∃₂ λ bs' eb → executeAndInsertBlockE-Either bs0 block ≡ Right (bs' , eb)

  open Reqs block (bs0 ^∙ bsInner)

  record ContractOk (bs' : BlockStore) (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≈ : NoHC1 → BlockIsValid (eb ^∙ ebBlock) (eb ^∙ ebId) → eb ^∙ ebBlock ≈Block block
      bsInv    : ∀ {eci}
                 → Preserves BlockStoreInv (bs0 , eci) (bs' , eci)
      -- executeAndInsertBlockE does not modify BlockTree fields other than btIDToBlock
      bs≡x : bs0 ≡ (bs' & (bsInner ∙ btIdToBlock) ∙~ (bs0 ^∙ bsInner ∙ btIdToBlock))

  Contract : EitherD-Post ErrLog (BlockStore × ExecutedBlock)
  Contract (Left x) = ⊤
  Contract (Right (bs' , eb)) = ContractOk bs' eb

  -- TUTORIAL: This proof has some additional commentary helping to understand the structure of the
  -- proof, and showing an example of how using abstract variants of functions makes proofs more
  -- resilient to change, as explained in
  -- https://github.com/oracle/bft-consensus-agda/blob/main/docs/PeerHandlerContracts.org
  contract' : EitherD-weakestPre step₀ Contract
  -- step₀ is a maybeSD in context of EitherD.  Therefore, via MonadMaybeD and EitherD-MonadMaybeD,
  -- this translates to EitherD-maybe.  We first deal with the easy case, applying the NoHC1
  -- function provided to ebBlock≈ to evidence eb≡ that eb is in btIdToBlock.
  proj₂ contract' eb eb≡ =
    mkContractOk (λ nohc _ → nohc eb≡ block-c) id refl
  proj₁ contract' getBlock≡nothing = contract₁
    where
    -- step₁ is again a maybeSD; if bs0 ^∙ bsRoot ≡ nothing, the Contract is trivial
    contract₁ : EitherD-weakestPre step₁ Contract
    proj₁ contract₁ _ = tt
    -- otherwise, bs0 ^∙ bsRoot ≡ just bsr, and we have an ifD; in the true branch, step₁ returns a
    -- Left, so again it is trivial
    proj₁ (proj₂ contract₁ bsr bsr≡) _ = tt
    -- in the else branch, we call step₂ bsr
    proj₂ (proj₂ contract₁ bsr bsr≡) btr<br = contract₂
      where
      contract₃ : ∀ eb → block ≡ (eb ^∙ ebBlock)
                  → EitherD-weakestPre (step₃ eb) Contract

      module EB = executeBlockESpec bs0 block
      open EB.ContractOk

      contract₂ : EitherD-weakestPre (step₂ bsr) Contract
      proj₂ contract₂ eb eb≡ ._             executeBlockE≡Right@refl
         with EitherD-contract (executeBlockE bs0 block) EB.Contract EB.contract
      ...| con rewrite executeBlockE-Either-ret eb≡ = contract₃ eb (ebBlock≡ con)
      proj₁ contract₂ (ErrCBlockNotFound _) executeBlockE≡Left = tt
      proj₁ contract₂ (ErrVerify _)         executeBlockE≡Left = tt
      proj₁ contract₂ (ErrInfo _)           executeBlockE≡Left = tt
      -- if executeBlockE returns Left (ErrECCBlockNotFound parentBlockId), then we have two casesdue to
      -- eitherSD (pathFromRoot parentBlockId bs0) LeftD λ blocksToReexecute →
      -- in the first case, we have a Left, so it's easy
      proj₁        (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) _ _ = tt
      -- in the second case, we have
      -- case⊎D (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
      -- and therefore two more cases; if the case⊎D returns Left, it's easy again
      proj₁ (proj₂ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) blocksToReexecute btr≡) _ _ = tt
      -- if the case⊎D in step₂ returns a Right, we call executeBlockE; this is an abstract EitherD
      -- variant, ensuring we must use the contract for executeBlockE because the proof cannot "look
      -- into" the implementation of executeBlockE, which makes the proof more resilient in case of
      -- changes in its implementation.
      proj₂ (proj₂ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) blocksToReexecute btr≡) _ _ =
        EB.contract' _ con⇒bindPost
        where
            con⇒bindPost : EitherD-Post-⇒ _ (EitherD-weakestPre-bindPost step₃ Contract)
            con⇒bindPost (Left _)  _   = tt
            con⇒bindPost (Right _) con = λ where eb' refl ._ refl → contract₃ eb' (EB.ContractOk.ebBlock≡ con) _ refl

      contract₃ eb refl _ _ = contract₄
        where

        contract₄ : EitherD-weakestPre (step₄ eb) Contract
        contract₄
           with insertBlockESpec.contract eb (bs0 ^∙ bsInner)
        ...| con = EitherD-⇒-bind (BlockTree.insertBlockE eb (bs0 ^∙ bsInner)) con con⇒bindPost
           where
             con⇒bindPost : ∀ r → insertBlockESpec.Contract eb (bs0 ^∙ bsInner) r → EitherD-weakestPre-bindPost _ Contract r
             con⇒bindPost (Left _) _                       = tt
             con⇒bindPost (Right (bt' , eb')) con' ._ refl =
               mkContractOk (λ nohc biv → IBE.blocks≈ nohc block-c)
                            btP bss≡x
               where
                 module IBE = insertBlockESpec.ContractOk con'

                 open BlockStoreInv

                 postulate -- TODO: placeholder, need to figure out how to get this here
                   eb0Valid : _

                 btP : ∀ {eci} → Preserves BlockStoreInv (bs0 , eci) ((bs0 & bsInner ∙~ bt') , eci)
                 btP (mkBlockStoreInv bti) = mkBlockStoreInv (IBE.btiPres eb0Valid bti)

                 bss≡x : bs0 ≡ (bs0 & bsInner ∙~ bt' & bsInner ∙ btIdToBlock ∙~ (bs0 ^∙ (bsInner ∙ btIdToBlock)))
                 bss≡x rewrite sym IBE.bt≡x = refl

  contract : Contract (executeAndInsertBlockE-Either bs0 block)
  contract rewrite executeAndInsertBlockE-Either-≡ =
    EitherD-contract (executeAndInsertBlockE.step₀ bs0 block) Contract contract'

module executeAndInsertBlockMSpec (vb : ValidBlock) where
  b = vbBlock vb

  -- NOTE: This function returns any errors, rather than producing them as output.
  module _ (pre : RoundManager) where
    bs = pre ^∙ lBlockStore

    contract
      : ∀ Post
        → (∀ e → {- At the moment we do not need to know why it failed -} Post (Left e) pre [])
        → ((isOk : executeAndInsertBlockESpec.Ok bs vb) → let (bs' , eb , _) = isOk in
             executeAndInsertBlockESpec.ContractOk bs vb bs' eb
           → Post (Right eb) (pre & rmBlockStore ∙~ bs') [])
        → LBFT-weakestPre (executeAndInsertBlockM b) Post pre
    proj₁ (contract Post pfBail pfOk ._ refl) e ≡left = pfBail e
    proj₂ (contract Post pfBail pfOk ._ refl) (bs' , eb) ≡right ._ refl unit refl
       with executeAndInsertBlockESpec.contract bs vb
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
        qcPost : ∈Post⇒∈PreOr (_≡ qc) pre post

    postulate -- TODO-2: prove
      contract' : LBFT-weakestPre (insertSingleQuorumCertM qc) Contract pre

    contract : ∀ Q → RWS-Post-⇒ Contract Q → LBFT-weakestPre (insertSingleQuorumCertM qc) Q pre
    contract Q pf = LBFT-⇒ (insertSingleQuorumCertM qc) pre contract' pf

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new (pre ^∙ lBlockStore ∙ bsHighestQuorumCert)
                 (pre ^∙ lBlockStore ∙ bsHighestCommitCert)
                 (pre ^∙ lBlockStore ∙ bsHighestTimeoutCert)

  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl = pf
