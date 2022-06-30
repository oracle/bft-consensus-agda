{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import Level
open import Optics.All
open import Util.ByteString
open import Util.Hash
import      Util.KVMap                                           as Map
open import Util.PKCS
open import Util.Prelude hiding (bail ; maybeSD ; pure ; return ; _>>=_)

------------------------------------------------------------------------------
open import Data.String                                          using (String)

module LibraBFT.Impl.Consensus.BlockStorage.BlockTree-AST where

postulate -- TODO-2: implement linkableBlockNew
  linkableBlockNew : ExecutedBlock → LinkableBlock

module addChild (lb : LinkableBlock) (hv : HashValue) where
  open import Dijkstra.AST.Either
  postulate -- TODO: implement it
    addChild-AST : EitherAST ErrLog LinkableBlock

module insertBlockE-AST (block : ExecutedBlock) (bt : BlockTree) where
  -- We hide EitherAST so that we can explicitly state the ErrLog type in
  -- function signatures to maintain consistency with the Haskell code
  open import Dijkstra.AST.Either ErrLog hiding (EitherAST)
  open import Dijkstra.AST.Either         using (EitherAST)

  open addChild

  insertBlockE-AST : EitherAST ErrLog (BlockTree × ExecutedBlock)
  insertBlockE-AST = do
    let blockId = block ^∙ ebId
    case btGetBlock blockId bt of λ where
      (just existingBlock) → return (bt , existingBlock)
      nothing → case btGetLinkableBlock (block ^∙ ebParentId) bt of λ where
        nothing → bail fakeErr
        (just parentBlock) → (do
          parentBlock' ← addChild-AST parentBlock blockId
          let bt' = bt & btIdToBlock ∙~ Map.kvm-insert-Haskell (block ^∙ ebParentId) parentBlock' (bt ^∙ btIdToBlock)
          return (  (bt' & btIdToBlock ∙~ Map.kvm-insert-Haskell blockId (LinkableBlock∙new block) (bt' ^∙ btIdToBlock))
               , block))

module insertQuorumCertE-AST (qc : QuorumCert) (bt0 : BlockTree) where
  -- We hide EitherAST so that we can explicitly state the ErrLog type in
  -- function signatures to maintain consistency with the Haskell code
  open import Dijkstra.AST.Either ErrLog hiding (EitherAST)
  open import Dijkstra.AST.Either         using (EitherAST)

  here' : List String → List String
  here' t = "BlockTree" ∷ "insertQuorumCert" ∷ t

  blockId = qc ^∙ qcCertifiedBlock ∙ biId

  safetyInvariant = forM_ (Map.elems (bt0 ^∙ btIdToQuorumCert)) $ \x →
          lcheck (   (x  ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash
                  ==  qc ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash)
                  ∨  (x  ^∙ qcCertifiedBlock ∙ biRound
                  /=  qc ^∙ qcCertifiedBlock ∙ biRound))
                 (here' ("failed check" ∷ "existing qc == qc || existing qc.round /= qc.round" ∷ []))

  continue1 : BlockTree → HashValue → ExecutedBlock → List InfoLog → (BlockTree × List InfoLog)
  continue2 : BlockTree → List InfoLog → (BlockTree × List InfoLog)

  insertQuorumCertE-AST : EitherAST ErrLog (BlockTree × List InfoLog)
  insertQuorumCertE-AST =
    case safetyInvariant of λ where
      (Left  e)    → bail e
      (Right unit) → maybeSD (btGetBlock blockId bt0) (bail fakeErr) λ block →
                     maybeSD (bt0 ^∙ btHighestCertifiedBlock) (bail fakeErr) λ hcb →
                     ifAST ⌊ (block ^∙ ebRound) >? (hcb ^∙ ebRound) ⌋
                     then
                       (let bt   = bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId
                                       & btHighestQuorumCert       ∙~ qc
                            info = (fakeInfo ∷ [])
                        in return (continue1 bt  blockId block info))
                     else
                          (return (continue1 bt0 blockId block []))

  continue1 bt blockId block info =
    continue2 ( bt & btIdToQuorumCert ∙~ lookupOrInsert blockId qc (bt ^∙ btIdToQuorumCert))
              ( (fakeInfo ∷ info) ++ (if ExecutedBlock.isNilBlock block then fakeInfo ∷ [] else [] ))

  continue2 bt info =
    if-dec (bt ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
    then ((bt & btHighestCommitCert ∙~ qc) , info)
    else (bt , info)

