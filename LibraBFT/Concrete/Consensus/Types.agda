open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap

module LibraBFT.Concrete.Consensus.Types where

  open import LibraBFT.Abstract.Types public hiding (Author)

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

  Author : Set
  Author = NodeId

  fakeAuthorsN : ℕ
  fakeAuthorsN = 4

  fakeAuthors : NodeId → Maybe (Fin fakeAuthorsN)
  fakeAuthors nid with nid <? fakeAuthorsN
  ...| yes xx = just (fromℕ≤ xx)
  ...| no  _  = nothing

  -- We want to associate PKs with all participants (not just those of the current epoch).  This is
  -- so we can verify signatures on fraudulent messages pretending to be authors of an epoch for
  -- accountability reasons, and also because that's what libra does.
  record PKI : Set where
    field
      pkAuthor : NodeId → PK
      pkInj    : ∀ (n₁ n₂ : NodeId)          -- Authors must have distinct public keys, otherwise a
               → pkAuthor n₁ ≡ pkAuthor n₂   -- dishonest author can potentially impersonate an honest
               → n₁ ≡ n₂                     -- author.
  open PKI public

  fakeEC : EpochId → EpochConfig
  fakeEC eid = record {
                 epochId           = eid
               ; authorsN          = fakeAuthorsN
               ; bizF              = 1
               ; isBFT             = s≤s (s≤s (s≤s (s≤s z≤n)))
               ; seed              = 0
               ; ecInitialState    = dummyHash
               ; initialAgreedHash = dummyHash
               ; isAuthor          = fakeAuthors

               }

  -- This is a placeholder for command type.  I haven't bothered making everything parameterized for
  -- this.  Maybe we shouldn't bother at all?

  TX : Set
  TX = ByteString

  Instant : Set
  Instant = ℕ   -- TODO: should be a time stamp

  --------------------------------------------------------------------------------------
  -- Below here is incremental progress towards something that will eventually mirror --
  -- LBFT.Consensus.Types in the Haskell repo.  Some types need to be migrated from   --
  -- LibraBFT.Concrete.Records                                                        --
  --------------------------------------------------------------------------------------


  HashValue : Set
  HashValue = Hash

  -----------------
  -- Information --
  -----------------

  record BlockInfo : Set where
    constructor mkBlockInfo
    field
      biEpoch : EpochId
      biRound : Round
      biId    : HashValue
      -- VCM: this has more fields...
  open BlockInfo public
  postulate instance enc-BlockInfo : Encoder BlockInfo

  record LedgerInfo : Set where
    constructor mkLedgerInfo
    field
      liCommitInfo        : BlockInfo
      liConsensusDataHash : HashValue
  open LedgerInfo public
  postulate instance enc-LedgerInfo : Encoder LedgerInfo

  liConsensusBlockId : LedgerInfo → HashValue
  liConsensusBlockId  = biId ∘ liCommitInfo

  record LedgerInfoWithSignatures : Set where
    constructor mkLedgerInfoWithSignatures
    field
      liwsLedgerInfo : LedgerInfo
      -- VCM: We also need vote orders in here, given that
      -- when a QC is sent, it contains agregated 'VoteData's, but
      -- not 'Vote'
      liwsSignatures : KVMap Author (Signature × Meta VoteOrder)
  open LedgerInfoWithSignatures public
  postulate instance enc-LedgerInfoWithSignatures : Encoder LedgerInfoWithSignatures

  -------------------
  -- Votes and QCs --
  -------------------

  record VoteData : Set where
    constructor mkVoteData
    field
      vdProposed : BlockInfo -- VCM-QUESTION: what's the difference?
      vdParent   : BlockInfo
  open VoteData public
  postulate instance enc-VoteData : Encoder VoteData

  record Vote : Set where
    constructor mkVote
    field
      vVoteData         : VoteData
      vAuthor           : Author
      vLedgerInfo       : LedgerInfo
      vSignature        : Signature
      vTimeoutSignature : Maybe Signature

      -- The algo should never /read/ vote order, so we place it
      -- in the Meta monad. 
      vOrder            : Meta VoteOrder
  open Vote public
  postulate instance enc-Vote : Encoder Vote

  record QuorumCert : Set where
    constructor mkQuorumCert
    field
      qcVoteData         : VoteData
      qcSignedLedgerInfo : LedgerInfoWithSignatures
  open QuorumCert public
  postulate instance enc-QuorumCert : Encoder QuorumCert

  qcCertifiedBlock : QuorumCert → BlockInfo
  qcCertifiedBlock  = vdProposed ∘ qcVoteData

  -- qcCertifiedBlock :: GetterNoFunctor QuorumCert BlockInfo
  -- qcCertifiedBlock  = to (^.qcVoteData.vdProposed)

  -- qcParentBlock :: GetterNoFunctor QuorumCert BlockInfo
  -- qcParentBlock  = to (^.qcVoteData.vdParent)

  -- qcLedgerInfo :: GetterNoFunctor QuorumCert LedgerInfoWithSignatures
  -- qcLedgerInfo  = to (^.qcSignedLedgerInfo)

  -- qcCommitInfo :: GetterNoFunctor QuorumCert BlockInfo
  -- qcCommitInfo  = to (^.qcSignedLedgerInfo.liwsLedgerInfo.liCommitInfo)

  -- qcRound :: GetterNoFunctor QuorumCert Round
  -- qcRound  = to (^.qcVoteData.vdProposed.biRound)

  -- qcEndsEpoch :: GetterNoFunctor QuorumCert Bool
  -- qcEndsEpoch  = to $ \qc -> isJust (qc^.qcSignedLedgerInfo.liwsLedgerInfo.liNextValidatorSet)

  qcVotesKV : QuorumCert → KVMap Author (Signature × Meta VoteOrder)
  qcVotesKV qc = liwsSignatures (qcSignedLedgerInfo qc)

  qcVotes : QuorumCert → List (Author × Signature × Meta VoteOrder)
  qcVotes qc = kvm-toList (qcVotesKV qc)

  qcCertifies : QuorumCert → Hash
  -- qcCertifies qc = biId (vdParent (qcVoteData qc))  -- MSM: Victor please confirm this change
  qcCertifies qc = biId (vdProposed (qcVoteData qc))
  ------------
  -- Blocks --
  ------------

  data BlockType (A : Set) : Set where
    Proposal : A → Author → BlockType A
    NilBlock : BlockType A
    Genesis  : BlockType A
  postulate instance enc-BlockType : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (BlockType A)

  record BlockData (A : Set) : Set where
    constructor mkBlockData
    field
      bdEpoch      : EpochId
      bdRound      : Round
      -- VCM-QUESTION: How do we represent the block that extends
      -- the genesis block? that block doesn't come with a QC.
      -- I'm guessing we just send one with a QC containing an empty map.
      bdQuorumCert : QuorumCert
      bdBlockType  : BlockType A
      -- VCM-QUESTION: I don't think we need this here...
      -- bdTimeStamp : Instant 
  open BlockData public
  postulate instance enc-BlockData : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (BlockData A)

  -- MSM: They use 'nothing' as the 'bSignature' when constructing a block to sign later.  This can be seen in the
  -- Haskell code at EventProcessor.hs:95-100 (commit f497bf9).  I think they also use "nothing"
  -- for the genesis block; this is based on what I see in genesis-block-store.txt, line 81
  -- (same commit).  Finally, "nil" blocks are not signed because they are produced
  -- independently by different validators.  IIRC, this is to enable committing after an
  -- epoch-changing command is processed: we cannot add more commands, but we need to add some
  -- quorum certificates in order to commit the epoch-changing command.
  record Block (A : Set) : Set where
    constructor mkBlock
    field
      bId        : HashValue
      bBlockData : BlockData A
      bSignature : Maybe Signature
  open Block public
  postulate instance enc-Block : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (Block A)

  -- bAuthor :: GetterNoFunctor (Block a) (Maybe Author)
  -- bAuthor  = to (^.bBlockData.bdAuthor)

  -- bEpoch :: GetterNoFunctor (Block a) Epoch
  -- bEpoch  = to (^.bBlockData.bdEpoch)

  -- bParentId :: GetterNoFunctor (Block a) HashValue
  -- bParentId  = to (^.bBlockData.bdQuorumCert.qcCertifiedBlock.biId)

  -- bPayload :: GetterNoFunctor (Block a) (Maybe a)
  -- bPayload  = to (^.bBlockData.bdPayload)

  -- bQuorumCert :: GetterNoFunctor (Block a) QuorumCert
  -- bQuorumCert  = to (^.bBlockData.bdQuorumCert)

  bRound : {a : Set} → (Block a) → Round
  bRound  = bdRound ∘ bBlockData

  -- bTimestamp :: GetterNoFunctor (Block a) Instant
  -- bTimestamp  = to (^.bBlockData.bdTimestamp)

  record SyncInfo : Set where
    constructor mkSyncInfo
    field
      siHighestQuorumCert  : QuorumCert
      siHighestCommitCert  : QuorumCert
      -- siHighestTimeoutCert : Mabe TimeoutCert -- VCM: TODO: define 
  postulate instance enc-SyncInfo : Encoder SyncInfo

  ----------------------
  -- Network Messages --
  ----------------------

  record ProposalMsg (A : Set) : Set where
    constructor mkProposalMsg
    field
      pmProposal : Block A
      pmSyncInfo : SyncInfo
  open ProposalMsg public
  postulate instance enc-ProposalMsg : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (ProposalMsg A)

  record VoteMsg : Set where
    constructor  mkVoteMsg
    field
      vmVote     : Vote
      vmSyncInfo : SyncInfo
  open VoteMsg public
  postulate instance enc-VoteMsg : Encoder VoteMsg

  -- This is a notification of a commit.  I don't think it's explicitly included in the Haskell/Rust
  -- code, but we need something to be able to express correctness conditions with.  It will
  -- probably have something different in it, but will serve the purpose for now.
  record CommitMsg : Set where
    constructor mkCommitMsg
    field
      cEpochId : EpochId
      cAuthor  : NodeId
      cRound   : Round
      cCert    : Hash
      cSigMB   : Maybe Signature
  open CommitMsg public
  postulate instance enc-CommitMsg : Encoder CommitMsg

  record LastVoteInfo : Set where
    constructor LastVoteInfo_new
    field
      lviLiDigest  : HashValue
      lviRound     : Round
      lviIsTimeout : Bool

  record PendingVotes : Set where
    constructor mkPendingVotes
    field
      pvLiDigestToVotes       : KVMap HashValue LedgerInfoWithSignatures
      -- pvRoundToTC             : KVMap Round TimeoutCertificate
      pvAuthorToLastVotedInfo : KVMap Author LastVoteInfo

  data ProcessedVMOutput : Set where        -- TODO: this is a placeholder
    processedVMOutput : ProcessedVMOutput

  record ExecutedBlock (a : Set) : Set where
    constructor ExecutedBlock_new
    field
      ebBlock  : Block a
      ebOutput : ProcessedVMOutput
  open ExecutedBlock public

-- ebEpoch :: GetterNoFunctor (ExecutedBlock a) Epoch
-- ebEpoch  = to (^.ebBlock.bEpoch)

  ebId : {a : Set} → ExecutedBlock a → HashValue
  ebId = bId ∘ ebBlock

-- ebId :: GetterNoFunctor (ExecutedBlock a) HashValue
-- ebId  = to (^.ebBlock.bId)

  ebQuorumCert : {a : Set} → ExecutedBlock a → QuorumCert
  ebQuorumCert = bdQuorumCert ∘ bBlockData ∘ ebBlock

-- ebQuorumCert : GetterNoFunctor (ExecutedBlock a) QuorumCert
-- ebQuorumCert  = to (^.ebBlock.bQuorumCert)

  ebParentId : {a : Set} → ExecutedBlock a → HashValue
  ebParentId = biId ∘ qcCertifiedBlock ∘ ebQuorumCert

-- ebParentId :: GetterNoFunctor (ExecutedBlock a) HashValue
-- ebParentId  = to (^.ebQuorumCert.qcCertifiedBlock.biId)

  ebRound : {a : Set} → ExecutedBlock a → Round
  ebRound = bRound ∘ ebBlock

-- ebRound :: GetterNoFunctor (ExecutedBlock a) Round
-- ebRound  = to (^.ebBlock.bRound)

-- ------------------------------------------------------------------------------

  record LinkableBlock (a : Set) : Set where
    constructor LinkableBlock_new
    field
      lbExecutedBlock : ExecutedBlock a
      -- lbChildren      : Set HashValue
  open LinkableBlock public

  lbId : {a : Set} → LinkableBlock a → HashValue
  lbId = ebId ∘ lbExecutedBlock

-- lbId :: GetterNoFunctor (LinkableBlock a) HashValue
-- lbId  = to (^.lbExecutedBlock.ebId)

-- lbEpoch :: GetterNoFunctor (LinkableBlock a) Epoch
-- lbEpoch  = to (^.lbExecutedBlock.ebEpoch)

-- lbRound :: GetterNoFunctor (LinkableBlock a) Round
-- lbRound  = to (^.lbExecutedBlock.ebRound)

  record BlockTree (a : Set) : Set where
    constructor mkBlockTree
    field
      btIdToBlock               : KVMap HashValue (LinkableBlock a)
      btRootId                  : HashValue
      btHighestCertifiedBlockId : HashValue
      btHighestQuorumCert       : QuorumCert
      -- btHighestTimeoutCert      : Maybe TimeoutCertificate
      btHighestCommitCert       : QuorumCert
      btPendingVotes            : PendingVotes
      btIdToQuorumCert          : KVMap HashValue QuorumCert
      btPrunedBlockIds          : List HashValue
      btMaxPrunedBlocksInMem    : ℕ
  open BlockTree public

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  -- This should not be used outside BlockTree.hs.
  btGetLinkableBlock : {a : Set} → HashValue -> BlockTree a -> Maybe (LinkableBlock a)
  btGetLinkableBlock hv bt = KVMap.lookup hv (btIdToBlock bt)

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  btGetBlock : {a : Set} → HashValue -> BlockTree a -> Maybe (ExecutedBlock a)
  btGetBlock hv bt = Maybe-map lbExecutedBlock (btGetLinkableBlock hv bt)

  btRoot : {a : Set}
         → (bt : BlockTree a)
         → ExecutedBlock a
  btRoot {a} bt with (btGetBlock (btRootId bt)) bt | inspect (btGetBlock (btRootId bt)) bt
  ...| just x  | _ = x
  ...| nothing | [ imp ] = ⊥-elim (assumedValid bt imp)
   where postulate
           assumedValid : (bt : BlockTree a) → btGetBlock (btRootId bt) bt ≡ nothing → ⊥

  record BlockStore (a : Set) : Set where
    constructor mkBlockStore
    field
      bsInner         : BlockTree a
      -- bsStateComputer : StateComputer a
      -- bsStorage       : CBPersistentStorage a
  open BlockStore public

  bsRoot : {a : Set} → BlockStore a → ExecutedBlock a
  bsRoot  = btRoot ∘ bsInner

  -- bsHighestCertifiedBlock :: GetterNoFunctor (BlockStore a) (ExecutedBlock a)
  -- bsHighestCertifiedBlock  = to (^.bsInner.btHighestCertifiedBlock)

  -- bsHighestQuorumCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestQuorumCert  = to (^.bsInner.btHighestQuorumCert)

  -- bsHighestCommitCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestCommitCert  = to (^.bsInner.btHighestCommitCert)

  -- bsHighestTimeoutCert :: GetterNoFunctor (BlockStore a) (Maybe TimeoutCertificate)
  -- bsHighestTimeoutCert  = to (^.bsInner.btHighestTimeoutCert)

  record EventProcessor (a : Set) : Set where
    constructor eventProcessor
    field
      myPK           : PK           -- TODO: this is temporary until we have a better model
      epEpochConfig  : EpochConfig  -- TODO: this should be a function of the "real" parts of EventProcessor
      -- TODO: for now, we omit the levels of indirection between BlockStore and BlockTree
      epBlockStore   : BlockStore a
  open EventProcessor public

  lBlockStore : {a : Set} → EventProcessor a → BlockStore a
  lBlockStore = epBlockStore

  lBlockTree : {a : Set} → EventProcessor a → BlockTree a
  lBlockTree = bsInner ∘ lBlockStore

-- ------------------------------------------------------------------------------


  postulate String : Set
  {-# BUILTIN STRING String #-}

  data Action (a : Set) : Set where
    BroadcastProposal : ProposalMsg a → Action a
    LogErr            : String        → Action a
    -- LogInfo           : InfoLog a     → Action a
    SendVote          : VoteMsg → List Author → Action a
  open Action public

-- data ErrLog a
--   = ErrBlockNotFound           ![Text] !HashValue
--   | ErrExistingBlock           ![Text] !(ExecutedBlock a) !HashValue !(ExecutedBlock a)
--   | ErrL                       ![Text]
--   | ErrParentBlockNotFound     ![Text] !HashValue
--   | ErrTestPlaceholder         ![Text] -- this should NEVER happen
--   | ErrVerify                  ![Text] VerifyError
--   deriving (Eq, Show)

-- data InfoLog a
--   = Info3ChainDetected                !(Block a)         !LedgerInfo
--   | InfoBlockTree                     ![Text]            !(BlockTree a)
--   | InfoBlockTreeShort                ![Text]            !(BlockTree a)
--   | InfoCommitting                    !(ExecutedBlock a)
--   | InfoEnter                         ![Text]
--   | InfoExit                          ![Text]
--   | InfoNewQuorumCertificate          !QuorumCert
--   | InfoNewRoundEvent                 !NewRoundEvent
--   | InfoUpdateHighestCertifiedBlockId !HashValue
--   | InfoUpdateHighestCommitCert       !QuorumCert
--   | InfoUpdateHighestQuorumCert       !QuorumCert
--   | InfoUpdateIdToBlockInsert         !(ExecutedBlock a)
--   | InfoUpdateIdToBlockDelete         !(ExecutedBlock a)
--   | InfoUpdateIdToQuorumCertInsert    !QuorumCert
--   | InfoUpdateLastVotedRound          !Round
--   | InfoUpdatePreferredRound          !Round
--   | InfoUpdateRootId                  !HashValue
--   | InfoL                             ![Text]
--   deriving (Eq, Show)


  -- Strange mixture of parameterization and not as I'm undecided which way to go.
  module WithState (State : Set) where
    module WithAction (Action : Set) where
     LBFT : (ReturnType : Set) → Set
     LBFT ReturnType = ∀ {state₀ : State} → {acts₀ : List Action} → ReturnType × State × List Action

  open WithState (EventProcessor TX) 
  open WithAction (Action TX) public

  -- This is an attempt to make our code look more like the Haskell code, even though we are faking
  -- the LBFT monad.  TODO: put it somewhere more appropriate.
  use : ∀ {t rt : Set} → (t → rt) → ∀ {x : t} → rt
  use f {x} = f x

