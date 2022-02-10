{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.BlockStorage.BlockTree       as BlockTree
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote          as Vote
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage    as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.StateComputerByteString      as SCBS
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import Optics.All
open import Util.ByteString
open import Util.Hash
open import Util.KVMap                                           as Map
open import Util.PKCS
open import Util.Prelude
------------------------------------------------------------------------------
open import Data.String                                          as String using (String)

module LibraBFT.Impl.Consensus.BlockStorage.BlockStore where

------------------------------------------------------------------------------

build
  : RootInfo      → RootMetadata
  → List Block    → List QuorumCert           → Maybe TimeoutCertificate
  → StateComputer → PersistentLivenessStorage → Usize
  → Either ErrLog BlockStore

module executeAndInsertBlockE-Types where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog (BlockStore × ExecutedBlock)

executeAndInsertBlockE         : BlockStore → Block → executeAndInsertBlockE-Types.VariantFor EitherD
executeAndInsertBlockE-Either  : BlockStore → Block → executeAndInsertBlockE-Types.VariantFor Either

executeBlockE
  : BlockStore → Block
  → EitherD ErrLog ExecutedBlock

executeBlockE-Either
  : BlockStore → Block
  → Either ErrLog ExecutedBlock

getBlock : HashValue → BlockStore → Maybe ExecutedBlock

insertSingleQuorumCertE
  : BlockStore → QuorumCert
  → Either ErrLog (BlockStore × List InfoLog)

pathFromRoot
  : HashValue → BlockStore
  → Either ErrLog (List ExecutedBlock)

pathFromRootM
  : HashValue
  → LBFT (Either ErrLog (List ExecutedBlock))

------------------------------------------------------------------------------

new
  : PersistentLivenessStorage → RecoveryData → StateComputer → Usize
  → Either ErrLog BlockStore
new storage initialData stateComputer maxPrunedBlocksInMem =
  build (initialData ^∙ rdRoot)
        (initialData ^∙ rdRootMetadata)
        (initialData ^∙ rdBlocks)
        (initialData ^∙ rdQuorumCerts)
        (initialData ^∙ rdHighestTimeoutCertificate)
        stateComputer
        storage
        maxPrunedBlocksInMem

abstract
  -- TODO: convert new to EitherD
  new-ed-abs : PersistentLivenessStorage → RecoveryData → StateComputer → Usize
             → EitherD ErrLog BlockStore
  new-ed-abs storage initialData stateComputer maxPrunedBlocksInMem = fromEither $
         new storage initialData stateComputer maxPrunedBlocksInMem

  new-e-abs : PersistentLivenessStorage → RecoveryData → StateComputer → Usize
            → Either ErrLog BlockStore
  new-e-abs = new
  new-e-abs-≡ : new-e-abs ≡ new
  new-e-abs-≡ = refl

build root _rootRootMetadata blocks quorumCerts highestTimeoutCert
           stateComputer storage maxPrunedBlocksInMem = do
  let (RootInfo∙new rootBlock rootQc rootLi) = root
      {- LBFT-OBM-DIFF : OBM does not implement RootMetadata
        assert_eq!(
            root_qc.certified_block().version(),
            root_metadata.version())
        assert_eq!(
            root_qc.certified_block().executed_state_id(),
            root_metadata.accu_hash)
      -}
      executedRootBlock = ExecutedBlock∙new
                            rootBlock
                            (StateComputeResult∙new (stateComputer ^∙ scObmVersion) nothing)
  tree ← BlockTree.new executedRootBlock rootQc rootLi maxPrunedBlocksInMem highestTimeoutCert
  bs1  ← (foldM) (λ bs b → fst <$> executeAndInsertBlockE-Either bs b)
                 (BlockStore∙new tree stateComputer storage)
                 blocks
  (foldM) go bs1 quorumCerts
 where
  go : BlockStore → QuorumCert
     → Either ErrLog BlockStore
  go bs qc = case insertSingleQuorumCertE bs qc of λ where
    (Left e)              → Left e
    (Right (bs' , _info)) → Right bs'

------------------------------------------------------------------------------

commitM
  : LedgerInfoWithSignatures
  → LBFT (Either ErrLog Unit)
commitM finalityProof = do
  bs ← use lBlockStore
  maybeSD (bs ^∙ bsRoot) (bail fakeErr) $ λ bsr → do
    let blockIdToCommit = finalityProof ^∙ liwsLedgerInfo ∙ liConsensusBlockId
    case getBlock blockIdToCommit bs of λ where
      nothing →
        bail (ErrCBlockNotFound blockIdToCommit)
      (just blockToCommit) →
        ifD‖ blockToCommit ^∙ ebRound ≤?ℕ bsr ^∙ ebRound ≔
             bail fakeErr -- "commit block round lower than root"
           ‖ otherwise≔ (pathFromRootM blockIdToCommit >>= λ where
                           (Left  e) → bail e
                           (Right r) → continue blockToCommit r)
 where
  continue : ExecutedBlock → List ExecutedBlock → LBFT (Either ErrLog Unit)
  continue blockToCommit blocksToCommit = do
    -- NOTE: Haskell tells the "StateComputer" to commit 'blocksToCommit'.
    -- TODO-1: The StateComputer might indicate an epoch change.
    -- NO NEED FOR PRUNING: pruneTreeM blockToCommit
    --
    -- THIS IS WHERE COMMIT IS COMPLETED.
    -- To connect to the proof's correctness condition, it will be necessary to
    -- send a CommitMsg, which will carry evidence of the CommitRule
    -- needed to invoke correctness conditions like ConcCommitsDoNotConflict*.
    -- The details of this connection yet have not been settled yet.
    -- TODO-1: Once the details are determined, then make the connection.
    ok unit

------------------------------------------------------------------------------

rebuildM : RootInfo → RootMetadata → List Block → List QuorumCert → LBFT (Either ErrLog Unit)
rebuildM root rootMetadata blocks quorumCerts = do
  -- logEE lEC (here []) $ do
  self0 ← use lBlockStore
  case build
         root rootMetadata blocks quorumCerts
         (self0 ^∙ bsHighestTimeoutCert)
         (self0 ^∙ bsStateComputer)
         (self0 ^∙ bsStorage)
         (self0 ^∙ bsInner ∙ btMaxPrunedBlocksInMem) of λ where
    (Left  e)    → bail e
    (Right (BlockStore∙new inner _ _)) → do
      toRemove ← BlockTree.getAllBlockIdM
      PersistentLivenessStorage.pruneTreeM toRemove ∙?∙  λ _ → do
       lRoundManager ∙ rmBlockStore ∙ bsInner ∙= inner
       self1 ← use lBlockStore
       maybeS (self1 ^∙ bsRoot) (bail fakeErr {-bsRootErrL here-}) $ λ bsr → do
        ifD self1 ^∙ bsHighestCommitCert ∙ qcCommitInfo ∙ biRound >? bsr ^∙ ebRound
          then
            (commitM (self1 ^∙ bsHighestCommitCert ∙ qcLedgerInfo) ∙^∙
              withErrCtx (here' ("commitM failed" ∷ [])) ∙?∙  λ _ →
              ok unit)
          else ok unit
 where
  here' : List String.String → List String.String
  here' t =
    "BlockStore" ∷ "rebuildM" ∷ t
    -- lsRI root : lsRMD rootMetadata : lsBs blocks : lsQCs quorumCerts : t

------------------------------------------------------------------------------

executeAndInsertBlockM : Block → LBFT (Either ErrLog ExecutedBlock)
executeAndInsertBlockM b = do
  bs ← use lBlockStore
  case⊎D executeAndInsertBlockE-Either bs b of λ where
    (Left e) → bail e
    (Right (bs' , eb)) → do
      lBlockStore ∙= bs'
      ok eb

module executeAndInsertBlockE (bs0 : BlockStore) (block : Block) where
  module VF where
    open executeAndInsertBlockE-Types public
  continue step₁ : VF.VariantFor EitherD
  continue = step₁

  step₂ : ExecutedBlock → VF.VariantFor EitherD
  step₃ : ExecutedBlock → VF.VariantFor EitherD
  step₄ : ExecutedBlock → VF.VariantFor EitherD

  step₀ =
    -- NOTE: if the hash is already in our blockstore, then HASH-COLLISION
    -- because we have already confirmed the new block is for the expected round
    -- and if there is already a block for that round then our expected round
    -- should be higher.
    maybeSD (getBlock (block ^∙ bId) bs0) continue (pure ∘ (bs0 ,_))

  here' : List String.String → List String.String
  here' t = "BlockStore" ∷ "executeAndInsertBlockE" {-∷ lsB block-} ∷ t

  step₁ =
      maybeSD (bs0 ^∙ bsRoot) (LeftD fakeErr) λ bsr →
      let btRound = bsr ^∙ ebRound in
      ifD btRound ≥?ℕ block ^∙ bRound
      then LeftD fakeErr -- block with old round
      else step₂ bsr

  step₂ _ = do
        eb ← case⊎D (executeBlockE-Either bs0 block) of λ where
          (Right res) → RightD res
          -- OBM-LBFT-DIFF : This is never thrown in OBM.
          -- It is thrown by StateComputer in Rust (but not in OBM).
          (Left (ErrECCBlockNotFound parentBlockId)) → do
            eitherSD (pathFromRoot parentBlockId bs0) LeftD λ blocksToReexecute →
              -- OBM-LBFT-DIFF : OBM StateComputer does NOT have state.
              -- If it ever does have state then the following 'forM' will
              -- need to change to some sort of 'fold' because 'executeBlockE'
              -- would change the state, so the state passed to 'executeBlockE'
              -- would no longer be 'bs0'.
              case⊎D (forM) blocksToReexecute (executeBlockE-Either bs0 ∘ (_^∙ ebBlock)) of λ where
                (Left  e) → LeftD e
                (Right _) → executeBlockE bs0 block
          (Left err) → LeftD err
        step₃ eb

  step₃ eb = do
        bs1 ← withErrCtxD'
                (here' [])
                -- TODO-1 : use inspect qualified so Agda List singleton can be in scope.
                (PersistentLivenessStorage.saveTreeE bs0 (eb ^∙ ebBlock ∷ []) [])
        step₄ eb

  step₄ eb = do
        (bt' , eb') ← BlockTree.insertBlockE eb (bs0 ^∙ bsInner)
        pure ((bs0 & bsInner ∙~ bt') , eb')

  E : VF.VariantFor Either
  E = toEither step₀

abstract
  executeAndInsertBlockE = executeAndInsertBlockE.step₀
  executeAndInsertBlockE-≡ : executeAndInsertBlockE ≡ executeAndInsertBlockE.step₀
  executeAndInsertBlockE-≡ = refl

  executeAndInsertBlockE-Either = executeAndInsertBlockE.E
  executeAndInsertBlockE-Either-≡ : executeAndInsertBlockE-Either ≡ executeAndInsertBlockE.E
  executeAndInsertBlockE-Either-≡ = refl

module executeBlockE (bs : BlockStore) (block : Block) where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog ExecutedBlock

  step₀ : VariantFor EitherD
  step₀ = do
    case SCBS.compute (bs ^∙ bsStateComputer) block (block ^∙ bParentId) of λ where
      (Left e)                   → LeftD fakeErr -- (here' e)
      (Right stateComputeResult) →
        pure (ExecutedBlock∙new block stateComputeResult)
   where
    here' : List String → List String
    here' t = "BlockStore" ∷ "executeBlockE" {-∷ lsB block-} ∷ t

  E : VariantFor Either
  E = toEither step₀

abstract
  executeBlockE = executeBlockE.step₀
  executeBlockE≡ : executeBlockE ≡ executeBlockE.step₀
  executeBlockE≡ = refl

  executeBlockE-Either = executeBlockE.E
  executeBlockE-Either-≡ : executeBlockE-Either ≡ executeBlockE.E
  executeBlockE-Either-≡ = refl

  executeBlockE-Either-ret : ∀ {bs block r} → executeBlockE-Either bs block ≡ r → EitherD-run (executeBlockE bs block) ≡ r
  executeBlockE-Either-ret refl = refl

------------------------------------------------------------------------------

insertSingleQuorumCertM
  : QuorumCert
  → LBFT (Either ErrLog Unit)
insertSingleQuorumCertM qc = do
  bs ← use lBlockStore
  case insertSingleQuorumCertE bs qc of λ where
    (Left  e)   → bail e
    (Right (bs' , info)) → do
      forM_ info logInfo
      lBlockStore ∙= bs'
      ok unit

insertSingleQuorumCertE bs qc =
  maybeS (getBlock (qc ^∙ qcCertifiedBlock ∙ biId) bs)
         (Left (ErrCBlockNotFound
                  -- (here ["insert QC without having the block in store first"])
                  (qc ^∙ qcCertifiedBlock ∙ biId)))
         (λ executedBlock →
             if ExecutedBlock.blockInfo executedBlock /= qc ^∙ qcCertifiedBlock
             then Left fakeErr
 --                      (ErrL (here [ "QC for block has different BlockInfo than EB"
 --                                  , "QC certified BI", show (qc ^∙ qcCertifiedBlock)
 --                                  , "EB BI", show (ExecutedBlock.blockInfo executedBlock)
 --                                  , "EB", show executedBlock ]))

             else (do
                    bs'           ← withErrCtx' (here' [])
                                      (PersistentLivenessStorage.saveTreeE bs [] (qc ∷ []))
                    (bt , output) ← BlockTree.insertQuorumCertE.E qc (bs' ^∙ bsInner)
                    pure ((bs' & bsInner ∙~ bt) , output)))
 where
  here' : List String.String → List String.String
  here' t = "BlockStore" ∷ "insertSingleQuorumCertE" ∷ t

------------------------------------------------------------------------------

insertTimeoutCertificateM : TimeoutCertificate → LBFT (Either ErrLog Unit)
insertTimeoutCertificateM tc = do
  curTcRound ← maybe {-(Round-} 0 {-)-} (_^∙ tcRound) <$> use (lBlockStore ∙ bsHighestTimeoutCert)
  ifD tc ^∙ tcRound ≤?ℕ curTcRound
    then ok unit
    else
      PersistentLivenessStorage.saveHighestTimeoutCertM tc ∙^∙ withErrCtx ("" ∷ []) ∙?∙ λ _ → do
        BlockTree.replaceTimeoutCertM tc
        ok unit

------------------------------------------------------------------------------

blockExists : HashValue → BlockStore → Bool
blockExists hv bs = Map.kvm-member hv (bs ^∙ bsInner ∙ btIdToBlock)

getBlock hv bs = btGetBlock hv (bs ^∙ bsInner)

getQuorumCertForBlock : HashValue → BlockStore → Maybe QuorumCert
getQuorumCertForBlock hv bs = Map.lookup hv (bs ^∙ bsInner ∙ btIdToQuorumCert)

pathFromRootM hv = pathFromRoot hv <$> use lBlockStore

pathFromRoot hv bs = BlockTree.pathFromRoot hv (bs ^∙ bsInner)

------------------------------------------------------------------------------

syncInfoM : LBFT SyncInfo
syncInfoM =
  SyncInfo∙new <$> use (lBlockStore ∙ bsHighestQuorumCert)
               <*> use (lBlockStore ∙ bsHighestCommitCert)
               <*> use (lBlockStore ∙ bsHighestTimeoutCert)

abstract
  syncInfoM-abs = syncInfoM
  syncInfoM-abs-≡ : syncInfoM-abs ≡ syncInfoM
  syncInfoM-abs-≡ = refl
