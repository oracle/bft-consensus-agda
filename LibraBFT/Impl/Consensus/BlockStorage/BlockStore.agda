{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree as BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote    as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

postulate
  insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either ErrLog Unit)
  getQuorumCertForBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe QuorumCert

------------------------------------------------------------------------------

getBlock : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Maybe ExecutedBlock

executeAndInsertBlockE
  : ∀ {𝓔}
  → BlockStore 𝓔 → Block
  → Either ErrLog (BlockStore 𝓔 × ExecutedBlock)

executeBlockE : ∀ {𝓔 : EpochConfig} → BlockStore 𝓔 → Block → Either ErrLog ExecutedBlock

pathFromRoot : ∀ {𝓔 : EpochConfig} → HashValue → BlockStore 𝓔 → Either ErrLog (List ExecutedBlock)

------------------------------------------------------------------------------

executeAndInsertBlockM : Block → LBFT (Either ErrLog ExecutedBlock)
executeAndInsertBlockM b = do
  s ← get
  let bs = rmGetBlockStore s
  caseM⊎ executeAndInsertBlockE bs b of λ where
    (Left e) → bail e
    (Right (bs' , eb)) → do
      put (rmSetBlockStore s bs')
      ok eb

executeAndInsertBlockE bs0 block =
  maybeS (getBlock (block ^∙ bId) bs0) continue (pure ∘ (bs0 ,_))
 where
  continue : Either ErrLog (BlockStore _ × ExecutedBlock)
  continue =
    maybeS (bs0 ^∙ bsRoot _) (Left fakeErr) λ bsr →
    let btRound = bsr ^∙ ebRound in
    if-dec btRound ≥?ℕ block ^∙ bRound
    then Left fakeErr -- block with old round
    else do
      eb ← case executeBlockE bs0 block of λ where
        (Right res) → Right res
        (Left (ErrBlockNotFound parentBlockId)) → do
          eitherS (pathFromRoot parentBlockId bs0) Left $ λ blocksToReexecute →
            case forM' blocksToReexecute (executeBlockE bs0 ∘ (_^∙ ebBlock)) of λ where
              (Left  e) → Left e
              (Right _) → executeBlockE bs0 block
        (Left err) → Left err
      -- bs1 <- withErrCtx' (here []) (PersistentLivenessStorage.saveTreeE bs0 [eb^.ebBlock] [])
      (bt' , eb') ← BlockTree.insertBlockE eb (bs0 ^∙ bsInner _)
      pure ((bs0 & bsInner _ ∙~  bt') , eb')

executeBlockE bs block =
  if is-nothing (getBlock (block ^∙ bParentId) bs)
    then Left (ErrBlockNotFound {-(here ["block with missing parent"])-} (block ^∙ bParentId))
    else {- do
      let compute            = bs ^. bsStateComputer.scCompute
          stateComputeResult = compute (bs^.bsStateComputer) block (block^.bParentId) -}
      pure (ExecutedBlock∙new block stateComputeResult)

------------------------------------------------------------------------------

getBlock hv bs = btGetBlock _ hv (bs ^∙ bsInner _)

pathFromRoot hv bs = BlockTree.pathFromRoot hv (bs ^∙ bsInner _)

------------------------------------------------------------------------------

syncInfoM : LBFT SyncInfo
syncInfoM = liftEC $
  SyncInfo∙new <$> use (lBlockStore ∙ bsHighestQuorumCert _)
               <*> use (lBlockStore ∙ bsHighestCommitCert _)
