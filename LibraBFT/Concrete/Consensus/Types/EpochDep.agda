open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap

open import LibraBFT.Concrete.Consensus.Types.EpochIndep

open import Optics.All

-- This module defines the types that depend on the epoch config
-- but never inspect it. Consequently, we define everyting over
-- an abstract ec passed around as a module parameter.
--
-- VCM: Later on I'd like to make the Optics.Reflection stuff work
-- with record parameters, so we can merge all modules back into Types,
-- for now, this is the easiest (note: making a module inside
-- Consensus.Types called EpochDep will break mkLens. I don't know why, but it does)
--
-- VCM: On another note; it does make sense to keep these types
-- concptually separate; they are different things! 
module LibraBFT.Concrete.Consensus.Types.EpochDep (ec : Meta EpochConfig) where

  record IsValidQC (qc : QuorumCert) : Set where
    field
      _ivqcSizeOk          : QuorumSize (unsafeReadMeta ec) ≤ length (qcVotes qc)
      _ivqcAuthors         : All ((_≢ nothing) ∘ isAuthor (unsafeReadMeta ec) ∘ proj₁) (qcVotes qc)
      _ivqcAuthorsDistinct : allDistinct (List-map (isAuthor (unsafeReadMeta ec) ∘ proj₁) (qcVotes qc))
  open IsValidQC public

  -- A block tree depends on a epoch config but works regardlesss of which
  -- epoch config we have. Moreover, this epoch config can't be changed internally
  -- to the block tree, hence, it really shouldn't be a field of the BlockTree.
  record BlockTree : Set where
    constructor mkBlockTree
    field
      _btIdToBlock               : KVMap HashValue LinkableBlock
      :btRootId                  : HashValue
      _btHighestCertifiedBlockId : HashValue
      _btHighestQuorumCert       : QuorumCert
      -- btHighestTimeoutCert      : Maybe TimeoutCertificate
      _btHighestCommitCert       : QuorumCert
      _btPendingVotes            : PendingVotes
      _btPrunedBlockIds          : List HashValue
      _btMaxPrunedBlocksInMem    : ℕ
      _btIdToQuorumCert          : KVMap HashValue (Σ QuorumCert IsValidQC)  -- TODO: IsValidQC should be Meta
  open BlockTree public
  unquoteDecl btIdToBlock   btRootId   btHighestCertifiedBlockId   btHighestQuorumCert
              btHighestCommitCert   btPendingVotes   btPrunedBlockIds
              btMaxPrunedBlocksInMem btIdToQuorumCert = mkLens (quote BlockTree)
             (btIdToBlock ∷ btRootId ∷ btHighestCertifiedBlockId ∷ btHighestQuorumCert ∷
              btHighestCommitCert ∷ btPendingVotes ∷ btPrunedBlockIds ∷
              btMaxPrunedBlocksInMem ∷ btIdToQuorumCert ∷ [])


  record BlockStore : Set where
    constructor mkBlockStore
    field
      :bsInner         : BlockTree
      -- bsStateComputer : StateComputer
      -- bsStorage       : CBPersistentStorage
  open BlockStore public
  unquoteDecl bsInner = mkLens (quote BlockStore)
             (bsInner ∷ [])

  -- bsHighestCertifiedBlock :: GetterNoFunctor (BlockStore a) (ExecutedBlock a)
  -- bsHighestCertifiedBlock  = to (^.bsInner.btHighestCertifiedBlock)

  -- bsHighestQuorumCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestQuorumCert  = to (^.bsInner.btHighestQuorumCert)

  -- bsHighestCommitCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestCommitCert  = to (^.bsInner.btHighestCommitCert)

  -- bsHighestTimeoutCert :: GetterNoFunctor (BlockStore a) (Maybe TimeoutCertificate)
  -- bsHighestTimeoutCert  = to (^.bsInner.btHighestTimeoutCert)

  -- These are the parts of the event processor that
  -- depend on a epoch config. We do not particularly care
  -- which epoch config they care about yet.
  --
  record EventProcessorWithEC : Set where
    constructor mkEventProcessor
    field
      :epBlockStore   : BlockStore
  open EventProcessorWithEC public
  unquoteDecl epBlockStore = mkLens (quote EventProcessorWithEC)
    (epBlockStore ∷ [])

  lBlockTree : Lens EventProcessorWithEC BlockTree
  lBlockTree = epBlockStore ∙ bsInner

