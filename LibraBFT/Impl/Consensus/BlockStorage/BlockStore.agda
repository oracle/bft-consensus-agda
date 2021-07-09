{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree    as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.Consensus.PersistentLivenessStorage as PersistentLivenessStorage
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

postulate
  commitM
    : LedgerInfoWithSignatures
    → LBFT (Either ErrLog Unit)

  insertSingleQuorumCertM
    : QuorumCert
    → LBFT (Either ErrLog Unit)

  insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either ErrLog Unit)
  getQuorumCertForBlock : HashValue → BlockStore → Maybe QuorumCert

------------------------------------------------------------------------------

getBlock : HashValue → BlockStore → Maybe ExecutedBlock

executeAndInsertBlockE : BlockStore → Block → Either ErrLog (BlockStore × ExecutedBlock)

executeBlockE : BlockStore → Block → Either ErrLog ExecutedBlock

pathFromRoot : HashValue → BlockStore → Either ErrLog (List ExecutedBlock)

------------------------------------------------------------------------------

executeAndInsertBlockM : Block → LBFT (Either ErrLog ExecutedBlock)
executeAndInsertBlockM b = do
  bs ← use lBlockStore
  caseM⊎ executeAndInsertBlockE bs b of λ where
    (Left e) → bail e
    (Right (bs' , eb)) → do
      lBlockStore ∙= bs'
      ok eb

executeAndInsertBlockE bs0 block =
  maybeS (getBlock (block ^∙ bId) bs0) continue (pure ∘ (bs0 ,_))
 where
  continue : Either ErrLog (BlockStore × ExecutedBlock)
  continue =
    maybeS (bs0 ^∙ bsRoot) (Left fakeErr) λ bsr →
    let btRound = bsr ^∙ ebRound in
    if-dec btRound ≥?ℕ block ^∙ bRound
    then Left fakeErr -- block with old round
    else do
      eb ← case executeBlockE bs0 block of λ where
        (Right res) → Right res
        (Left (ErrBlockNotFound parentBlockId)) → do
          eitherS (pathFromRoot parentBlockId bs0) Left $ λ blocksToReexecute →
            case (forM) blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
              (Left  e) → Left e
              (Right _) → executeBlockE bs0 block
        (Left err) → Left err
      bs1 ← {-withErrCtx' (here [])-}
            -- TODO-1 : use inspect qualified so Agda List singleton can be in scope.
            (PersistentLivenessStorage.saveTreeE bs0 ((eb ^∙ ebBlock) ∷ []) [])
      (bt' , eb') ← BlockTree.insertBlockE eb (bs0 ^∙ bsInner)
      pure ((bs0 & bsInner ∙~  bt') , eb')

executeBlockE bs block =
  if is-nothing (getBlock (block ^∙ bParentId) bs)
    then Left (ErrBlockNotFound {-(here ["block with missing parent"])-} (block ^∙ bParentId))
    else {- do
      let compute            = bs ^. bsStateComputer.scCompute
          stateComputeResult = compute (bs^.bsStateComputer) block (block^.bParentId) -}
      pure (ExecutedBlock∙new block stateComputeResult)

------------------------------------------------------------------------------

getBlock hv bs = btGetBlock hv (bs ^∙ bsInner)

pathFromRoot hv bs = BlockTree.pathFromRoot hv (bs ^∙ bsInner)

------------------------------------------------------------------------------

syncInfoM : LBFT SyncInfo
syncInfoM =
  SyncInfo∙new <$> use (lBlockStore ∙ bsHighestQuorumCert)
               <*> use (lBlockStore ∙ bsHighestCommitCert)
