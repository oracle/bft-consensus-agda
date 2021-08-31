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
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
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

open Invariants
open RoundManagerTransProps
open QCProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module executeBlockESpec (bs : BlockStore) (block : Block) where

  Ok : Set
  Ok = ∃[ eb ] (executeBlockE bs block ≡ Right eb)

  record ContractOk (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≡ : block ≡ eb ^∙ ebBlock

  postulate -- TODO: prove
    contract : (isOk : Ok) → ContractOk (proj₁ isOk)

module executeAndInsertBlockESpec (bs0 : BlockStore) (block : Block) where
  open executeAndInsertBlockE bs0 block

  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree

  blockId = block ^∙ bId

  ------   These are used only outside this module.  
  Ok : Set
  Ok = ∃₂ λ bs' eb → executeAndInsertBlockE bs0 block ≡ Right (bs' , eb)

  private
    Ok' : BlockStore → ExecutedBlock → Either ErrLog (BlockStore × ExecutedBlock) → Set
    Ok' bs' eb m = m ≡ Right (bs' , eb)

  Err : Set
  Err = ∃[ e ] (executeAndInsertBlockE bs0 block ≡ Left e)
  ------

  open Reqs block blockId (bs0 ^∙ bsInner)

  record ContractOk (bs' : BlockStore) (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      ebBlock≈ : ReqNewBlock → ReqPreBlock → NoHC1 → eb ^∙ ebBlock ≈Block block
      bsInv    : ReqNewBlock → ∀ {eci}
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
  -- this translates to EitherD-maybe.  We first deal with the easy case.
  proj₂ contract' eb eb≡ =
    mkContractOk ebBlock≈ (const id) refl
    where
    ebBlock≈ : ReqNewBlock → ReqPreBlock → NoHC1 → eb ^∙ ebBlock ≈Block block
    ebBlock≈ rnb rpb _ = hash≡⇒≈Block {b2 = block} (rpb eb≡) rnb

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
      contract₃ : ∀ eb → block ≡ eb ^∙ ebBlock
                  → EitherD-weakestPre (step₃ eb) Contract

      module EB = executeBlockESpec bs0 block

      contract₂ : EitherD-weakestPre (step₂ bsr) Contract
      proj₂ contract₂ eb eb≡ ._             executeBlockE≡Right@refl = contract₃ eb (EB.ContractOk.ebBlock≡ (EB.contract (eb , eb≡)))
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
      -- if the case⊎D returns a Right, we call executeBlockE₀ (the EitherD variant).  We use executeBlockE≡ to handle case
      -- analysis on the result of calling the abstract executeBlockE variant, ensuring we must use the contract for
      -- executeBlockE because the proof cannot "look into" the implementation of executeBlockE, which makes the proof
      -- more resilient in case of changes in its implementation.
      -- TODO-2: clean this up by writing a general version of the contract for executeBlockE
      proj₂ (proj₂ (proj₁ contract₂ (ErrECCBlockNotFound parentBlockId) executeBlockE≡Left) blocksToReexecute btr≡) _ _
        with  executeBlockE bs0  block | inspect
             (executeBlockE bs0) block
      ... | Left  x | [ R ] rewrite executeBlockE≡ R = tt
      ... | Right y | [ R ] rewrite executeBlockE≡ R =
        λ where c refl ._ refl →
                  contract₃ c (EB.ContractOk.ebBlock≡ (EB.contract (c , R)))
                            _ refl

      contract₃ eb refl _ _ = contract₄
        where

        contract₄ : EitherD-weakestPre (step₄ eb) Contract
        contract₄
           with insertBlockESpec.contract eb (bs0 ^∙ bsInner)
        ...| con
           with BlockTree.insertBlockE.E eb (bs0 ^∙ bsInner)
        ...| Left _ = tt
        ...| Right (bt' , eb') =
           λ where ._ refl → mkContractOk IBE.blocks≈ btP bss≡x
           where
           module IBE = insertBlockESpec.ContractOk con

           open BlockStoreInv

           btP : ReqNewBlock → ∀ {eci} → Preserves BlockStoreInv (bs0 , eci) ((bs0 & bsInner ∙~ bt') , eci)
           btP rnb (mkBlockStoreInv bti) = mkBlockStoreInv (IBE.btiPres rnb bti)

           bss≡x : bs0 ≡ (bs0 & bsInner ∙~ bt' & bsInner ∙ btIdToBlock ∙~ (bs0 ^∙ (bsInner ∙ btIdToBlock)))
           bss≡x rewrite sym IBE.bt≡x = refl

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
        qcPost : ∈Post⇒∈PreOr (_≡ qc) pre post

    postulate -- TODO-2: prove
      contract' : LBFT-weakestPre (insertSingleQuorumCertM qc) Contract pre

    contract : ∀ Q → RWS-Post-⇒ Contract Q → LBFT-weakestPre (insertSingleQuorumCertM qc) Q pre
    contract Q pf = LBFT-⇒ Contract Q pf (insertSingleQuorumCertM qc) pre contract'

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new (pre ^∙ lBlockStore ∙ bsHighestQuorumCert)
                 (pre ^∙ lBlockStore ∙ bsHighestCommitCert)
                 (pre ^∙ lBlockStore ∙ bsHighestTimeoutCert)

  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl = pf
