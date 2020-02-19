open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap

open import Optics.All

open import Data.String using (String)

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
      _biEpoch : EpochId
      _biRound : Round
      _biId    : HashValue
      -- VCM: this has more fields...
  open BlockInfo public
  unquoteDecl biEpoch   biRound   biId = mkLens (quote BlockInfo)
             (biEpoch ∷ biRound ∷ biId ∷ [])
  postulate instance enc-BlockInfo : Encoder BlockInfo

  record LedgerInfo : Set where
    constructor mkLedgerInfo
    field
      _liCommitInfo        : BlockInfo
      _liConsensusDataHash : HashValue
  open LedgerInfo public
  unquoteDecl liCommitInfo   liConsensusBlockId = mkLens (quote LedgerInfo)
             (liCommitInfo ∷ liConsensusBlockId ∷ [])
  postulate instance enc-LedgerInfo : Encoder LedgerInfo

  record LedgerInfoWithSignatures : Set where
    constructor mkLedgerInfoWithSignatures
    field
      _liwsLedgerInfo : LedgerInfo
      -- VCM: We also need vote orders in here, given that
      -- when a QC is sent, it contains agregated 'VoteData's, but
      -- not 'Vote'
      _liwsSignatures : KVMap Author (Signature × Meta VoteOrder)
  open LedgerInfoWithSignatures public
  unquoteDecl liwsLedgerInfo   liwsSignatures = mkLens (quote LedgerInfoWithSignatures)
             (liwsLedgerInfo ∷ liwsSignatures ∷ [])
  postulate instance enc-LedgerInfoWithSignatures : Encoder LedgerInfoWithSignatures

  -------------------
  -- Votes and QCs --
  -------------------

  record VoteData : Set where
    constructor mkVoteData
    field
      _vdProposed : BlockInfo
      _vdParent   : BlockInfo
  open VoteData public
  unquoteDecl vdProposed   vdParent = mkLens (quote VoteData)
             (vdProposed ∷ vdParent ∷ [])
  postulate instance enc-VoteData : Encoder VoteData

  record Vote : Set where
    constructor mkVote
    field
      _vVoteData         : VoteData
      _vAuthor           : Author
      _vLedgerInfo       : LedgerInfo
      _vSignature        : Signature
      _vTimeoutSignature : Maybe Signature

      -- The algo should never /read/ vote order, so we place it
      -- in the Meta monad. 
      _vOrder            : Meta VoteOrder
  open Vote public
  unquoteDecl vVoteData   vAuthor   vLedgerInfo   vSignature   vTimeoutSignature = mkLens (quote Vote)
             (vVoteData ∷ vAuthor ∷ vLedgerInfo ∷ vSignature ∷ vTimeoutSignature ∷ [])
  postulate instance enc-Vote : Encoder Vote

  record QuorumCert : Set where
    constructor mkQuorumCert
    field
      _qcVoteData         : VoteData
      _qcSignedLedgerInfo : LedgerInfoWithSignatures
  open QuorumCert public
  unquoteDecl qcVoteData   qcSignedLedgerInfo = mkLens (quote QuorumCert)
             (qcVoteData ∷ qcSignedLedgerInfo ∷ [])
  postulate instance enc-QuorumCert : Encoder QuorumCert

  qcCertifiedBlock : Lens QuorumCert BlockInfo
  qcCertifiedBlock = qcVoteData ∙ vdProposed

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
  qcVotesKV = _liwsSignatures ∘ _qcSignedLedgerInfo

  qcVotes : QuorumCert → List (Author × Signature × Meta VoteOrder)
  qcVotes qc = kvm-toList (qcVotesKV qc)

  qcCertifies : Lens QuorumCert  Hash
  qcCertifies = qcVoteData ∙ vdProposed ∙ biId

  _qcCertifies : QuorumCert → Hash
  _qcCertifies q = q ^∙ qcCertifies 

  module WithEC (ec : EpochConfig) where

    record IsValidQCAuthor (_ : Author) : Set where
      field
        _ivaIdx : EpochConfig.Author ec
    open IsValidQCAuthor public

    record IsValidQC (qc : QuorumCert) : Set where
      field
        _ivqcSizeOk       : QuorumSize ec ≤ length (qcVotes qc)
        _ivqcValidAuthors : All ((IsValidQCAuthor ∘ proj₁) ) (qcVotes qc)
  open WithEC public

  ------------
  -- Blocks --
  ------------

  data BlockType : Set where
    Proposal : TX → Author → BlockType
    NilBlock : BlockType
    Genesis  : BlockType
  postulate instance enc-BlockType : Encoder BlockType

  record BlockData : Set where
    constructor mkBlockData
    field
      _bdEpoch      : EpochId
      _bdRound      : Round
      -- VCM-QUESTION: How do we represent the block that extends
      -- the genesis block? that block doesn't come with a QC.
      -- I'm guessing we just send one with a QC containing an empty map.
      _bdQuorumCert : QuorumCert
      _bdBlockType  : BlockType
      -- VCM-QUESTION: I don't think we need this here...
      -- bdTimeStamp : Instant
  open BlockData public
  unquoteDecl bdEpoch   bdRound   bdQuorumCert   bdBlockType = mkLens (quote BlockData)
             (bdEpoch ∷ bdRound ∷ bdQuorumCert ∷ bdBlockType ∷ [])
  postulate instance enc-BlockData : Encoder BlockData

  -- MSM: They use 'nothing' as the 'bSignature' when constructing a block to sign later.  This can be seen in the
  -- Haskell code at EventProcessor.hs:95-100 (commit f497bf9).  I think they also use "nothing"
  -- for the genesis block; this is based on what I see in genesis-block-store.txt, line 81
  -- (same commit).  Finally, "nil" blocks are not signed because they are produced
  -- independently by different validators.  IIRC, this is to enable committing after an
  -- epoch-changing command is processed: we cannot add more commands, but we need to add some
  -- quorum certificates in order to commit the epoch-changing command.
  record Block : Set where
    constructor mkBlock
    field
      _bId        : HashValue
      _bBlockData : BlockData
      _bSignature : Maybe Signature
  open Block public
  unquoteDecl bId   bBlockData   bSignature = mkLens (quote Block)
             (bId ∷ bBlockData ∷ bSignature ∷ [])
  postulate instance enc : Encoder Block

  -- bAuthor :: GetterNoFunctor (Block a) (Maybe Author)
  -- bAuthor  = to (^.bBlockData.bdAuthor)

  -- bEpoch :: GetterNoFunctor (Block a) Epoch
  -- bEpoch  = to (^.bBlockData.bdEpoch)

  -- bParentId :: GetterNoFunctor (Block a) HashValue
  -- bParentId  = to (^.bBlockData.bdQuorumCert.qcCertifiedBlock.biId)

  -- bPayload :: GetterNoFunctor (Block a) (Maybe a)
  -- bPayload  = to (^.bBlockData.bdPayload)

  bQuorumCert : Lens Block QuorumCert
  bQuorumCert  = bBlockData ∙ bdQuorumCert

  -- bQuorumCert :: GetterNoFunctor (Block a) QuorumCert
  -- bQuorumCert  = to (^.bBlockData.bdQuorumCert)

  bRound : Lens Block Round
  bRound =  bBlockData ∙ bdRound

  -- bTimestamp :: GetterNoFunctor (Block a) Instant
  -- bTimestamp  = to (^.bBlockData.bdTimestamp)

  record SyncInfo : Set where
    constructor mkSyncInfo
    field
      _siHighestQuorumCert  : QuorumCert
      _siHighestCommitCert  : QuorumCert
      -- _siHighestTimeoutCert : Mabe TimeoutCert -- VCM: TODO: define
  open SyncInfo public
  unquoteDecl siHighestQuorumCert   siHighestCommitCert = mkLens (quote SyncInfo)
             (siHighestQuorumCert ∷ siHighestCommitCert ∷ [])
  postulate instance enc-SyncInfo : Encoder SyncInfo

  ----------------------
  -- Network Messages --
  ----------------------

  record ProposalMsg : Set where
    constructor mkProposalMsg
    field
      _pmProposal : Block
      _pmSyncInfo : SyncInfo
  open ProposalMsg public
  unquoteDecl pmProposal   pmSyncInfo = mkLens (quote ProposalMsg)
             (pmProposal ∷ pmSyncInfo ∷ [])
  postulate instance enc-ProposalMsg : Encoder ProposalMsg

  record VoteMsg : Set where
    constructor  mkVoteMsg
    field
      _vmVote     : Vote
      _vmSyncInfo : SyncInfo
  open VoteMsg public
  unquoteDecl vmVote   vmSyncInfo = mkLens (quote VoteMsg)
             (vmVote ∷ vmSyncInfo ∷ [])
  postulate instance enc-VoteMsg : Encoder VoteMsg

  -- This is a notification of a commit.  I don't think it's explicitly included in the Haskell/Rust
  -- code, but we need something to be able to express correctness conditions with.  It will
  -- probably have something different in it, but will serve the purpose for now.
  record CommitMsg : Set where
    constructor mkCommitMsg
    field
      _cEpochId : EpochId
      _cAuthor  : NodeId
      _cRound   : Round
      _cCert    : Hash
      _cSigMB   : Maybe Signature
  open CommitMsg public
  unquoteDecl cEpochId   cAuthor   cRound   cCert   cSigMB = mkLens (quote CommitMsg)
             (cEpochId ∷ cAuthor ∷ cRound ∷ cCert ∷ cSigMB ∷ [])
  postulate instance enc-CommitMsg : Encoder CommitMsg

  record LastVoteInfo : Set where
    constructor LastVoteInfo_new
    field
      _lviLiDigest  : HashValue
      _lviRound     : Round
      _lviIsTimeout : Bool
  open LastVoteInfo public

  record PendingVotes : Set where
    constructor mkPendingVotes
    field
      _pvLiDigestToVotes       : KVMap HashValue LedgerInfoWithSignatures
      -- _pvRoundToTC             : KVMap Round TimeoutCertificate
      _pvAuthorToLastVotedInfo : KVMap Author LastVoteInfo
  open PendingVotes public

  data ProcessedVMOutput : Set where        -- TODO: this is a placeholder
    processedVMOutput : ProcessedVMOutput

  record ExecutedBlock : Set where
    constructor ExecutedBlock_new
    field
      _ebBlock  : Block
      _ebOutput : ProcessedVMOutput
  open ExecutedBlock public
  unquoteDecl ebBlock   ebOutput = mkLens (quote ExecutedBlock)
             (ebBlock ∷ ebOutput ∷ []) 
-- ebEpoch :: GetterNoFunctor (ExecutedBlock a) Epoch
-- ebEpoch  = to (^.ebBlock.bEpoch)

  ebId : Lens ExecutedBlock HashValue
  ebId = ebBlock ∙ bId

-- ebId :: GetterNoFunctor (ExecutedBlock a) HashValue
-- ebId  = to (^.ebBlock.bId)

  ebQuorumCert : Lens ExecutedBlock QuorumCert
  ebQuorumCert = ebBlock ∙ bQuorumCert

-- ebQuorumCert : GetterNoFunctor (ExecutedBlock a) QuorumCert
-- ebQuorumCert  = to (^.ebBlock.bQuorumCert)

  ebParentId : Lens ExecutedBlock HashValue
  ebParentId = ebQuorumCert ∙ qcCertifiedBlock ∙ biId

-- ebParentId :: GetterNoFunctor (ExecutedBlock a) HashValue
-- ebParentId  = to (^.ebQuorumCert.qcCertifiedBlock.biId)

  ebRound : Lens ExecutedBlock Round
  ebRound = ebBlock ∙ bRound

-- ebRound :: GetterNoFunctor (ExecutedBlock a) Round
-- ebRound  = to (^.ebBlock.bRound)

-- ------------------------------------------------------------------------------

  record LinkableBlock : Set where
    constructor LinkableBlock_new
    field
      _lbExecutedBlock : ExecutedBlock
      -- _lbChildren      : Set HashValue
  open LinkableBlock public
  unquoteDecl lbExecutedBlock = mkLens (quote LinkableBlock)
             (lbExecutedBlock ∷ [])

  lbId : Lens LinkableBlock HashValue
  lbId = lbExecutedBlock ∙ ebId

-- lbId :: GetterNoFunctor (LinkableBlock a) HashValue
-- lbId  = to (^.lbExecutedBlock.ebId)

-- lbEpoch :: GetterNoFunctor (LinkableBlock a) Epoch
-- lbEpoch  = to (^.lbExecutedBlock.ebEpoch)

-- lbRound :: GetterNoFunctor (LinkableBlock a) Round
-- lbRound  = to (^.lbExecutedBlock.ebRound)

  record BlockTree : Set where
    constructor mkBlockTree
    field
      _btIdToBlock               : KVMap HashValue LinkableBlock
      _btRootId                  : HashValue
      _btHighestCertifiedBlockId : HashValue
      _btHighestQuorumCert       : QuorumCert
      -- btHighestTimeoutCert      : Maybe TimeoutCertificate
      _btHighestCommitCert       : QuorumCert
      _btPendingVotes            : PendingVotes
      _btPrunedBlockIds          : List HashValue
      _btMaxPrunedBlocksInMem    : ℕ
      -- These two are kept at the end as we don't want to define lenses for them because they are
      -- not simple types, and it seems the lenses defined below must be for a prefix of the fields
      -- in the record.
      _btEpochConfig             : Meta EpochConfig
      _btIdToQuorumCert          : KVMap HashValue (Σ QuorumCert (WithEC.IsValidQC (unsafeReadMeta _btEpochConfig)))
  open BlockTree public
  unquoteDecl btIdToBlock   btRootId   btHighestCertifiedBlockId   btHighestQuorumCert
              btHighestCommitCert   btPendingVotes   btPrunedBlockIds
              btMaxPrunedBlocksInMem = mkLens (quote BlockTree)
             (btIdToBlock ∷ btRootId ∷ btHighestCertifiedBlockId ∷ btHighestQuorumCert ∷
              btHighestCommitCert ∷ btPendingVotes ∷ btPrunedBlockIds ∷
              btMaxPrunedBlocksInMem ∷ [])

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  -- This should not be used outside BlockTree.hs.
  btGetLinkableBlock : HashValue -> BlockTree -> Maybe LinkableBlock
  btGetLinkableBlock hv bt = KVMap.lookup hv (bt ^∙ btIdToBlock)

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  btGetBlock : HashValue -> BlockTree -> Maybe ExecutedBlock
  btGetBlock hv bt = Maybe-map _lbExecutedBlock (btGetLinkableBlock hv bt)

  btRoot : BlockTree → ExecutedBlock
  btRoot bt with (btGetBlock (bt ^∙ btRootId)) bt | inspect (btGetBlock (bt ^∙ btRootId)) bt
  ...| just x  | _ = x
  ...| nothing | [ imp ] = ⊥-elim (assumedValid bt imp)
   where postulate
           -- VCM: Isn't this a very dangerous postulate here?
           -- I think our btRoot should return a Maybe or should receive
           -- this postulate as a parameter... 
           assumedValid : (bt : BlockTree) → btGetBlock (bt ^∙ btRootId) bt ≡ nothing → ⊥

  record BlockStore : Set where
    constructor mkBlockStore
    field
      _bsInner         : BlockTree
      -- bsStateComputer : StateComputer
      -- bsStorage       : CBPersistentStorage
  open BlockStore public
  unquoteDecl bsInner = mkLens (quote BlockStore)
             (bsInner ∷ [])

  bsRoot : BlockStore → ExecutedBlock
  bsRoot = btRoot ∘ _bsInner

  -- bsHighestCertifiedBlock :: GetterNoFunctor (BlockStore a) (ExecutedBlock a)
  -- bsHighestCertifiedBlock  = to (^.bsInner.btHighestCertifiedBlock)

  -- bsHighestQuorumCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestQuorumCert  = to (^.bsInner.btHighestQuorumCert)

  -- bsHighestCommitCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestCommitCert  = to (^.bsInner.btHighestCommitCert)

  -- bsHighestTimeoutCert :: GetterNoFunctor (BlockStore a) (Maybe TimeoutCertificate)
  -- bsHighestTimeoutCert  = to (^.bsInner.btHighestTimeoutCert)

  record EventProcessor : Set where
    constructor eventProcessor
    field
      _epEpochConfig  : EpochConfig  -- TODO: this should be a function of the "real" parts of EventProcessor
      _epBlockStore   : BlockStore
      _epValidators   : List Author  -- TODO: ValidatorVerifier details
  open EventProcessor public
  unquoteDecl epEpochConfig   epBlockStore epValidators = mkLens (quote EventProcessor)
             (epEpochConfig ∷ epBlockStore ∷ epValidators ∷ [])

  lBlockStore : Lens EventProcessor BlockStore
  lBlockStore = epBlockStore

  lBlockTree : Lens EventProcessor BlockTree
  lBlockTree = lBlockStore ∙ bsInner

-- ------------------------------------------------------------------------------

  data Action : Set where
    BroadcastProposal : ProposalMsg           → Action
    LogErr            : String                → Action
    -- LogInfo           : InfoLog a          → Action
    SendVote          : VoteMsg → List Author → Action
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

