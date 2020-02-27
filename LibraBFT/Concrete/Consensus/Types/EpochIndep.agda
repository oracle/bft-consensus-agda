open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.Util.KVMap as KVMap

open import Optics.All

open import Data.String using (String)

-- Defines the types that /DO NOT/ depend on an epoch config.
module LibraBFT.Concrete.Consensus.Types.EpochIndep where

  open import LibraBFT.Abstract.Types public hiding (Author)

  -- Below here is incremental progress towards something 
  -- that will eventually mirror the types in LBFT.Consensus.Types
  -- that /DO NOT/ depend on the set of active authors
  -- or safety rules, which we call the /EpochConfig/.

  Author : Set
  Author = NodeId

  AccountAddress : Set
  AccountAddress = Author  -- TODO: comment in Haskell code indicates this will change

  _≟AccountAddress_ : (a₁ a₂ : AccountAddress) → Dec (a₁ ≡ a₂)
  _≟AccountAddress_ = _≟_

  HashValue : Set
  HashValue = Hash

  TX : Set
  TX = ByteString

  Instant : Set
  Instant = ℕ   -- TODO: should be a time stamp

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

-- ------------------------------------------------------------------------------

  -- Note BlockTree and BlockStore are defined in EpochDep.agda as they depend on an EpochConfig

  record PersistentStorage : Set where
    constructor mkPersistentStorage
    field
      :psEpoch          : EpochId
      -- :psLastVotedRound : Round
      -- :psPreferredRound : Round
  open PersistentStorage public
  unquoteDecl psEpoch = mkLens (quote PersistentStorage)
    (psEpoch ∷ [])

  record ValidatorSigner : Set where
    constructor mkValidatorSigner
    field
      :vsAuthor     : AccountAddress  -- TODO: Not quite faithful to Haskell code, which may change
      -- :vsPublicKey  : PK
      -- :vsPrivateKey : SK   -- MSM: Is it OK that this is here?  The SystemModel
                              -- doesn't allow one node to examine another's state,
                              -- so I think it's OK: we don't model someone being able
                              -- to impersonate someone else.
  open ValidatorSigner public

  record ValidatorInfo : Set where
    constructor mkValidatorInfo
    field
      :viPublicKey   : String  -- TODO: this should be PK but have to settle down definition first
      -- :viVotingPower : Int  -- TODO: For now we consider each validator to have one
                               --       vote.  Generalize later.
  open ValidatorInfo public

  record ValidatorVerifier : Set where
    constructor mkValidatorVerifier
    field
      :vvAddressToValidatorInfo : (KVMap AccountAddress ValidatorInfo)
      :vvQuorumVotingPower      : ℕ  -- TODO: for now, this is QuorumSize
      -- :vvTotalVotingPower    : ℕ  -- TODO: commented out as I'm not sure what it's for
  open ValidatorVerifier public
  unquoteDecl vvAddressToValidatorInfo vvQuorumVotingPower = mkLens 
    (quote ValidatorVerifier) 
    (vvAddressToValidatorInfo ∷ vvQuorumVotingPower ∷ [])

  record SafetyRules : Set where
    constructor mkSafetyRules
    field
      :srPersistentStorage : PersistentStorage
      -- :srValidatorSigner   : ValidatorSigner
  open SafetyRules public
  unquoteDecl srPersistentStorage = mkLens (quote SafetyRules) 
   (srPersistentStorage ∷ [])

  -- Note EventProcessor is defined in EventProcessor.agda as it depends on an EpochConfig
  -- MSM: why not put it in EpochDep then, like BlockTree and BlockStore

  data Action : Set where
    BroadcastProposal : ProposalMsg           → Action
    -- VCM: why are we bothering with logging in Agda?
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

