{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap as Map
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
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.OBM.Prelude
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

      qcPost : QCProps.∈Post⇒∈PreOrBT (_≡ block ^∙ ebBlock ∙ bQuorumCert) bt“ bt

module insertQuorumCertESpec
  (qc : QuorumCert) (bt0  : BlockTree) where
  open insertQuorumCertE qc bt0

  Ok : Set
  Ok = ∃₂ λ bt1 il → insertQuorumCertE qc bt0 ≡ Right (bt1 , il)

  private
    Ok' : BlockTree → List InfoLog → Either ErrLog (BlockTree × List InfoLog) → Set
    Ok' bt il m = m ≡ Right (bt , il)

  Contract : Either ErrLog (BlockTree × List InfoLog) → Set
  Contract (Left _) = Unit
  Contract (Right (bt1 , il)) = ∈Post⇒∈PreOrBT (_≡ qc) bt0 bt1
                              -- TODO: this is only part of what we need.  We want to also prove
                              -- that QCs in the pre are also in the post.  Make a record?

  contract : (isOk : Ok) → let (bt1 , il , _) = isOk in Contract (Right (bt1 , il))
  contract (bt1 , il , isOk)
     with safetyInvariant
  ...| Right unit
    with pf1 isOk
    where
    pf1 : Ok' bt1 il (step₁ blockId) → ∃[ block ] (just block ≡ btGetBlock blockId bt0 × Ok' bt1 il (step₂ blockId block))
    pf1 isOk
       with  btGetBlock blockId bt0
    ...| just block = block , refl , isOk
  ...| block , lookupJust₁ , step2-ok
    with pf2 step2-ok
    where
    pf2 : Ok' bt1 il (step₂ blockId block) → ∃[ hcb ](just hcb ≡ bt0 ^∙ btHighestCertifiedBlock × Ok' bt1 il (step₃ blockId block hcb))
    pf2 isOk
       with bt0 ^∙ btHighestCertifiedBlock
    ...| just hcb   = hcb , refl , isOk
  ...| hcb , lookupJust₂ , step3-ok
    with          bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId &    btHighestQuorumCert ∙~ qc
       | inspect (bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId &_) (btHighestQuorumCert ∙~ qc)
       | fakeInfo ∷ []
  ...| bt₃-true | [ R ] | il₃-true
    with  if ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋ then bt₃-true else   bt0               | inspect
         (if ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋ then bt₃-true else_) bt0               |
          if ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋ then il₃-true else   []                | inspect
         (if ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋ then il₃-true else_) []
  ...| bt₃ | [ refl ] | il₃ | [ refl ]
    with  bt₃ &    btIdToQuorumCert ∙~ lookupOrInsert blockId qc (bt₃ ^∙ btIdToQuorumCert)     | inspect
         (bt₃ &_) (btIdToQuorumCert ∙~ lookupOrInsert blockId qc (bt₃ ^∙ btIdToQuorumCert))    |
          (fakeInfo ∷ il₃) ++   (if ExecutedBlock.isNilBlock block then fakeInfo ∷ [] else []) | inspect
         ((fakeInfo ∷ il₃) ++_) (if ExecutedBlock.isNilBlock block then fakeInfo ∷ [] else [])
  ...| bt-c₁ | [ refl ] | il-c₁ | [ refl ]
    with pf3 step3-ok
    where
    pf3 : Ok' bt1 il (step₃ blockId block hcb) → ∈Post⇒∈PreOrBT (_≡ qc) bt0 bt₃
                                               × continue1 bt₃ blockId block il₃ ≡ (bt1 , il)
    proj₂ (pf3 isOk)
      with ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋
          -- I thought I might be stuck with pure vs. Right, so made the silly xxx below, but now if
          -- I try to put refl in the hole below, I see something about NilBlock in the error,
          -- suggesting it's looking into continue2.  Maybe I could try making an abstract alias for
          -- continue2 and working with that, but it feels like I'm in the weeds, so taking a break
          -- here and sharing in case someone else has some insight.
    ... | false = xxx isOk (obm-dangerous-magic' "stuck here, see notes above") 
       where
         xxx : ∀ {A : Set} {a : A} {x : A} {y : Either ErrLog A} → y ≡ Right a → pure x ≡ y → x ≡ a
         xxx {A} {a} {x} refl refl = refl
    ... | true  =  obm-dangerous-magic' "TODO: first resolve 'easy' case above"
    proj₁ (pf3 isOk) qc' qc'∈bt₃ = obm-dangerous-magic' "TODO: very similar to two proofs below, not identical, generalise?"

  ...| bt0→bt3 , continue1-ok
    with pf-continue1 continue1-ok
    where
    pf-continue1 : continue1 bt₃ blockId block il₃ ≡ (bt1 , il)
                 → ∈Post⇒∈PreOrBT (_≡ qc) bt0 bt-c₁
                 × continue2 bt-c₁ il-c₁ ≡ (bt1 , il)
    proj₂ (pf-continue1 refl) = refl
    proj₁ (pf-continue1 refl)  = ∈Post⇒∈PreOrBT-trans (_≡ qc) bt0→bt3 bt3→bt-c1
      where
        bt3→bt-c1 : ∈Post⇒∈PreOrBT (_≡ qc) bt₃ bt-c₁
        bt3→bt-c1 qc' qc'∈bt-c₁
           with Map.kvm-member blockId (bt₃ ^∙ btIdToQuorumCert)
        ... | true  = Left qc'∈bt-c₁
        ... | false
           with qc'∈bt-c₁
        ... | inHQC x = Left (inHQC x)
        ... | inHCC x = Left (inHCC x)
  ...| bt0→bt-c₁ , continue2-ok = pf-continue2 continue2-ok
    where
    pf-continue2 : continue2 bt-c₁ il-c₁ ≡ (bt1 , il) → Contract (Right (bt1 , il))
    pf-continue2 refl = ∈Post⇒∈PreOrBT-trans (_≡ qc) {bt0} {bt-c₁} {bt1} bt0→bt-c₁ bt-c₁→bt1
      where
      bt-c₁→bt1 : _
      bt-c₁→bt1 qc' qc'∈bt1
         with (bt-c₁ ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
      ...| no  hcR≥qcR = Left qc'∈bt1
      ...| yes hcR<qcR
        with qc'∈bt1
      ...| inHQC x = Left (inHQC x)
      ...| inHCC x = Right x
