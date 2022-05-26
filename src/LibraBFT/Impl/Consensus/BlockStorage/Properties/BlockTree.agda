{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Dijkstra.AST.Branching
open import Dijkstra.AST.Core
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.Records using (BlockId-correct)
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Consensus.BlockStorage.BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.ByteString
open import Util.Hash
open import Util.KVMap                                           as Map
open import Util.Lemmas
open import Util.PKCS
open import Util.Prelude

open import Dijkstra.AST.Either ErrLog renaming (EitherD to EitherAST)

open QCProps
open Invariants

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree where

module addChildSpec (lb : LinkableBlock) (hv : HashValue) where

  open addChild lb hv

  record ContractOk (lb' : LinkableBlock) : Set where
    field
      presLB : lb ≡L lb' at lbExecutedBlock
  open ContractOk

  Contract : Either ErrLog LinkableBlock → Set
  Contract (Left _) = ⊤
  Contract (Right lb') = ContractOk lb'

  postulate -- TODO: prove after implementing addChild
    contract'-AST : ASTPredTrans.predTrans EitherPT addChild-AST Contract unit

  contract-AST : Contract (runEither addChild-AST unit)
  contract-AST = ASTSufficientPT.sufficient EitherSuf addChild-AST Contract unit contract'-AST


module insertBlockESpec
         (eb0 : ExecutedBlock)
         (eb0Valid : BlockIsValid (eb0 ^∙ ebBlock) (eb0 ^∙ ebId))
         (bt : BlockTree)
  where
  eb0Id = eb0 ^∙ ebId

  -- A straightforward proof that the EitherD variant of insertBlockE has the same behaviour as the
  -- Either variant that closely mirrors the original Haskell code.  The proof is not trivially
  -- achieved by `refl`, as is the case for some similar situations (e.g.,
  -- ensureRoundAndSyncUpM-original-≡) because Agda does not know that we need to perform case
  -- analysis on the result of runnning addChild.
  insertBlockE-original-≡ : ∀ {block bt}
                            → insertBlockE-original block bt ≡ EitherD-run (insertBlockE block bt)
  insertBlockE-original-≡ {block} {bt} rewrite insertBlockE-≡
     with btGetBlock (block ^∙ ebId) bt
  ... | just _  = refl
  ... | nothing
     with btGetLinkableBlock (block ^∙ ebParentId) bt
  ... | nothing = refl
  ... | just parentBlock rewrite addChild-≡-E1 parentBlock (block ^∙ ebId)
     with EitherD-run (addChild parentBlock (block ^∙ ebId))
  ... | Left  x = refl
  ... | Right y = refl

  open Reqs (eb0 ^∙ ebBlock) bt

  record ContractOk (bt“ : BlockTree) (eb : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      bt≡x    : bt ≡ (bt“ & btIdToBlock ∙~ (bt ^∙ btIdToBlock))
      blocks≈ : NoHC1 → eb [ _≈Block_ ]L eb0 at ebBlock
      btiPres : ∀ {eci} → Preserves BlockTreeInv (bt , eci) (bt“ , eci)

  Contract : Either ErrLog (BlockTree × ExecutedBlock) → Set
  Contract (Left _) = ⊤
  Contract (Right (bt' , b)) = ContractOk bt' b

  open insertBlockE

  postulate -- TODO-1: prove; note that the contract is stronger than we need because insertBlockE
            -- is called only when btGetBlock eb0Id bt ≡ nothing in LibraBFT
    contract' : EitherD-weakestPre (step₀ eb0 bt) Contract

  contract : EitherD-weakestPre (insertBlockE eb0 bt) Contract
  contract rewrite insertBlockE-≡ = contract'

  -- A contract (not used yet) for the Either version
  contract-E : Contract (insertBlockE.E eb0 bt)
  contract-E = EitherD-contract (step₀ eb0 bt) Contract contract'

  open insertBlockE-AST eb0 bt
  open addChild

  contract'-AST : ASTPredTrans.predTrans EitherPT insertBlockE-AST Contract unit
  contract'-AST
     with  btGetBlock (eb0 ^∙ ebId)  bt | inspect
          (btGetBlock (eb0 ^∙ ebId)) bt
  ... | just existingBlock | [ R ] =
          mkContractOk refl
                       (λ nohc → nohc {existingBlock} R (BlockIsValid.bidCorr eb0Valid))
                       id
  ... | nothing | [ R ]
    with  btGetLinkableBlock (eb0 ^∙ ebParentId)  bt | inspect
         (btGetLinkableBlock (eb0 ^∙ ebParentId)) bt
  ... | nothing | _ = tt
  ... | just parentBlock | [ R' ] =
          ASTPredTransMono.predTransMono EitherPTMono
            (addChild-AST parentBlock (eb0 ^∙ ebId))
            (addChildSpec.Contract parentBlock (eb0 ^∙ ebId))
            _
            Contract⊆
            unit
            (addChildSpec.contract'-AST  parentBlock (eb0 ^∙ ebId))

         where
           btInsert : BlockTree → HashValue → LinkableBlock → BlockTree
           btInsert bt bid lb = bt & btIdToBlock ∙~ Map.kvm-insert-Haskell bid lb (bt ^∙ btIdToBlock)

           pres-AVB : ∀ {bt : BlockTree} → AllValidBlocks bt
                      → {bid : HashValue} {lb : LinkableBlock}
                      → BlockIsValid ((lb ^∙ lbExecutedBlock) ^∙ ebBlock) bid
                      → AllValidBlocks (btInsert bt bid lb)
           pres-AVB {bt} hyp {bid} {lb} biv {bid'} {eb} ij
             with bid' ≟Hash bid
           ...| no  neq  rewrite sym (insert-target-≢-Haskell {v = lb} {kvm = bt ^∙ btIdToBlock} neq) = hyp ij
           ...| yes refl rewrite lookup-correct-haskell {k = bid} {v = lb} {kvm = bt ^∙ btIdToBlock}
                               | just-injective ij = biv

           module _ (parentBlock' : LinkableBlock)
                    (parentValid  : BlockIsValid ((parentBlock' ^∙ lbExecutedBlock) ^∙ ebBlock) (eb0 ^∙ ebParentId))
                    (ebValid      : BlockIsValid (eb0 ^∙ ebBlock) (eb0 ^∙ ebId)) where
             bt' : BlockTree
             bt' = btInsert bt (eb0 ^∙ ebParentId) parentBlock'

             bt'' : BlockTree
             bt'' = btInsert bt' (eb0 ^∙ ebId) (LinkableBlock∙new eb0)

             finalAllValidBlocks : AllValidBlocks bt → AllValidBlocks bt''
             finalAllValidBlocks avb = pres-AVB {bt'} (pres-AVB {bt} avb parentValid) ebValid

           Contract⊆ : _
           Contract⊆ (Left _)    _                    .(Left _)             refl = tt
           Contract⊆ (Right parentBlock') addChildCon .(Right parentBlock') refl = con
             where
             con : _
             con = mkContractOk
                          refl
                          (λ _ → refl)
                          λ bti → mkBlockTreeInv
                                    (BlockTreeInv.allValidQCs bti)
                                    (finalAllValidBlocks parentBlock'
                                                         (biv (BlockTreeInv.allValidBlocks bti))
                                                         eb0Valid
                                                         (BlockTreeInv.allValidBlocks bti))
                    where

                      -- Because rewrite directly in biv1 did not work for some reason
                      biv' : AllValidBlocks bt → _ → _
                      biv' avb refl
                         with avb (btGetBlock≡ {bt = bt} R')
                      ...| bv = mkBlockIsValid (BlockIsValid.bidCorr {bid = eb0 ^∙ ebParentId} bv)
                                               (BlockIsValid.bhashCorr bv)
                      biv : AllValidBlocks bt → _
                      biv avb = biv' avb (sym (cong (_^∙ ebBlock) (addChildSpec.ContractOk.presLB addChildCon)))

  contract-AST : Contract (runEither insertBlockE-AST unit)
  contract-AST = ASTSufficientPT.sufficient EitherSuf insertBlockE-AST Contract unit contract'-AST

module insertQuorumCertESpec
  (qc : QuorumCert) (bt0  : BlockTree) where
  open insertQuorumCertE qc bt0

  record ContractOk (btPre btPost : BlockTree) (ilPre ilPost : List InfoLog) : Set where
    constructor mkContractOk
    field
      noNewQCs : ∈Post⇒∈PreOrBT (_≡ qc) btPre btPost

  ContractOk-trans : ∀ {btPre btInt btPost ilPre ilInt ilPost}
                   → ContractOk btPre btInt  ilPre ilInt
                   → ContractOk btInt btPost ilInt ilPost
                   → ContractOk btPre btPost ilPre ilPost
  ContractOk-trans (mkContractOk noNewQCs) (mkContractOk noNewQCs₁) =
                    mkContractOk (∈Post⇒∈PreOr'-trans _∈BlockTree_ (_≡ qc) noNewQCs noNewQCs₁)

  Contract : EitherD-Post ErrLog (BlockTree × List InfoLog)
  Contract (Left _) = ⊤
  Contract (Right (bt1 , il)) = ContractOk bt0 bt1 [] il

  contract' : EitherD-weakestPre step₀ Contract
  contract'
     with safetyInvariant
  ...| Left e     = tt
  ...| Right unit = contract-step₁'
    where
    contract-step₁' : EitherD-weakestPre (step₁ blockId) Contract
    proj₁ contract-step₁' _ = tt
    proj₂ contract-step₁' block _ = contract-step₂'
      where
      contract-step₂' : EitherD-weakestPre (step₂ blockId block) Contract
      proj₁ contract-step₂' _ = tt
      proj₂ contract-step₂' hcb _ =
        contract-step₃'
        where
        contract-cont2' : ∀ (bt : BlockTree) (info : List InfoLog)
                         → let (bt' , info') = continue2 bt info
                           in ContractOk bt bt' info info'
        contract-cont2' bt info
           with (bt ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
        ...| yes hqcR<qcR = mkContractOk (∈BlockTree-upd-hcc refl refl)
        ...| no  hqcR≥qcR = mkContractOk (λ _ x → inj₁ x)

        cont1-update-bt : BlockTree → BlockTree
        cont1-update-bt bt = bt & btIdToQuorumCert ∙~ Map.insert blockId qc (bt ^∙ btIdToQuorumCert)

        info' : List InfoLog → Bool → List InfoLog
        info' il b = (fakeInfo ∷ il) ++ (if b then (fakeInfo ∷ []) else [])

        contract-cont1' : ∀ (btPre : BlockTree) (infoPre : List InfoLog)
                        → let (btPost , infoPost) = continue1 btPre blockId block infoPre
                          in  ContractOk btPre btPost infoPre infoPost
        contract-cont1' btPre infoPre
           with Map.kvm-member blockId (btPre ^∙ btIdToQuorumCert)
        ...| true  = mkContractOk (ContractOk.noNewQCs (contract-cont2' btPre (info' infoPre $ ExecutedBlock.isNilBlock block )))
        ...| false = ContractOk-trans {btInt = cont1-update-bt btPre} {ilInt = info' infoPre $ ExecutedBlock.isNilBlock block }
                               (mkContractOk (∈Post⇒∈PreOrBT-QCs≡ _ refl refl))
                               (mkContractOk (ContractOk.noNewQCs (contract-cont2'
                                                                     (cont1-update-bt btPre)
                                                                     (info' infoPre $ ExecutedBlock.isNilBlock block))))

        bt' = bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId
                  & btHighestQuorumCert       ∙~ qc

        contract-step₃' : EitherD-weakestPre (step₃ blockId block hcb) Contract
        proj₁ contract-step₃' _ = ContractOk-trans
                                    (mkContractOk (∈BlockTree-upd-hqc refl refl))
                                    (contract-cont1' bt' (fakeInfo ∷ []))
        proj₂ contract-step₃' _ = ContractOk-trans
                                    (mkContractOk (∈Post⇒∈PreOr'-refl _∈BlockTree_ _))
                                    (contract-cont1' bt0 [])

module insertQuorumCertE-ASTSpec
  (qc : QuorumCert) (bt0  : BlockTree) where
  open insertQuorumCertE-AST qc bt0

  -- The following definitions are the same as for the EitherD version above
  record ContractOk (btPre btPost : BlockTree) (ilPre ilPost : List InfoLog) : Set where
    constructor mkContractOk
    field
      noNewQCs : ∈Post⇒∈PreOrBT (_≡ qc) btPre btPost

  ContractOk-trans : ∀ {btPre btInt btPost ilPre ilInt ilPost}
                   → ContractOk btPre btInt  ilPre ilInt
                   → ContractOk btInt btPost ilInt ilPost
                   → ContractOk btPre btPost ilPre ilPost
  ContractOk-trans (mkContractOk noNewQCs) (mkContractOk noNewQCs₁) =
                    mkContractOk (∈Post⇒∈PreOr'-trans _∈BlockTree_ (_≡ qc) noNewQCs noNewQCs₁)

  Contract : Either ErrLog (BlockTree × List InfoLog) → Set
  Contract (Left x) = ⊤
  Contract (Right (bt1 , il)) = ContractOk bt0 bt1 [] il

  -- Here we prove the weakest precondition for insertQuorumCertE-AST to ensure Contract The proof
  -- is similar to the corresponding one for insertQuorumCertE above, but the AST framework makes it
  -- easier to discover the proof obligations.  Note that the code for insertQuorumCertE-AST is not
  -- broken explicitly into steps because we don't need to write the types of the individual proofs
  -- because the framework presents them to us.
  contract-AST : ASTPredTrans.predTrans EitherPTExt insertQuorumCertE-AST Contract unit
  contract-AST with safetyInvariant
  --  The Left/bail cases are easy, as Contract simply requires ⊤ in this case.
  ... | Left _ = tt
  ... | Right unit =
      -- Two proof obligations are introduced due to the use of maybeSD; the AST framework with the
      -- branching extensions ensures that the two goals are created by typing C-c C-r in a hole
      -- here.  To understand why, see the definition of maybeSD, which is in terms of the maybeD
      -- field of the relevant MonadMaybeD instance (EitherDASTExt-MonadMaybeD), which translates to
      -- ASTop (Right (BCmaybe mb)).  The opPT field of BranchPT establishes that we require two
      -- proofs, one for the nothing case and one for the just case; each receives evidence that mb
      -- is the relevant case (nothing or just something), and determines the relevant proof
      -- obligation.
      const tt , λ block _ →
      -- Similarly, another use of maybeSD in the code results in automatically introducing two
      -- proof obligations using C-c C-r
      const tt ,
      -- The "Right" goal in this case is determined by the use of ifAST in the code, which
      -- translates to ASTop (Right (BCif b)) ... (see BranchingSyntax).  Therefore, in this case,
      -- the proof obligation is determined in PredTransExtension to have two proof obligations, one
      -- for the case in which b is true and one for b is false.  Each gets evidence of the value of
      -- b (not used in this example) and the predicate transformer resulting from passing the value
      -- of b to the function in the definition of ASTPredTrans.opPT yields the proof obligation.
      -- The proofs for each case here are more or less copied from the insertQuorumcertESpec proof,
      -- but because the framework guided us to the goals, we did not need to state their types
      -- explicitly, which in turn means that we did not need to break the code into explicit steps.
      λ _ _ →
      (const $ let bt' = bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId
                             & btHighestQuorumCert       ∙~ qc
                in ContractOk-trans
                     (mkContractOk (∈BlockTree-upd-hqc refl refl))
                     (contract-cont1' block bt' (fakeInfo ∷ [])))
      , (const $ ContractOk-trans
                   (mkContractOk (∈Post⇒∈PreOr'-refl _∈BlockTree_ _))
                   (contract-cont1' block bt0 []))
      where
      -- The following proofs are just about pure code, and are copied verbatim from
      -- insertQuorumCertESpec above
      contract-cont2' : ∀ (bt : BlockTree) (info : List InfoLog)
                       → let (bt' , info') = continue2 bt info
                         in ContractOk bt bt' info info'
      contract-cont2' bt info
         with (bt ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
      ...| yes hqcR<qcR = mkContractOk (∈BlockTree-upd-hcc refl refl)
      ...| no  hqcR≥qcR = mkContractOk (λ _ x → inj₁ x)

      cont1-update-bt : BlockTree → BlockTree
      cont1-update-bt bt = bt & btIdToQuorumCert ∙~ Map.insert blockId qc (bt ^∙ btIdToQuorumCert)

      info' : List InfoLog → Bool → List InfoLog
      info' il b = (fakeInfo ∷ il) ++ (if b then (fakeInfo ∷ []) else [])

      contract-cont1' : ∀ (block : ExecutedBlock) (btPre : BlockTree) (infoPre : List InfoLog)
                      → let (btPost , infoPost) = continue1 btPre blockId block infoPre
                        in  ContractOk btPre btPost infoPre infoPost
      contract-cont1' block btPre infoPre
         with Map.kvm-member blockId (btPre ^∙ btIdToQuorumCert)
      ...| true  = mkContractOk (ContractOk.noNewQCs (contract-cont2' btPre (info' infoPre $ ExecutedBlock.isNilBlock block )))
      ...| false = ContractOk-trans {btInt = cont1-update-bt btPre} {ilInt = info' infoPre $ ExecutedBlock.isNilBlock block }
                             (mkContractOk (∈Post⇒∈PreOrBT-QCs≡ _ refl refl))
                             (mkContractOk (ContractOk.noNewQCs (contract-cont2'
                                                                   (cont1-update-bt btPre)
                                                                 (info' infoPre $ ExecutedBlock.isNilBlock block))))

