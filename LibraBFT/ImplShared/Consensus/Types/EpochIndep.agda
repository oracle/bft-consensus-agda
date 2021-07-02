{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap            as KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String using (String)

-- Defines the types that /DO NOT/ depend on an epoch config.
-- TODO-3: update types to reflect more recent version of LibraBFT.  This is
-- a substantial undertaking that should probably be led by someone who can
-- access our internal implementation.

module LibraBFT.ImplShared.Consensus.Types.EpochIndep where
  -- Below here is incremental progress towards something
  -- that will eventually mirror the types in LBFT.Consensus.Types
  -- that /DO NOT/ depend on the set of active authors
  -- or safety rules, which we call the /EpochConfig/.

  Author : Set
  Author = NodeId

  AccountAddress : Set
  AccountAddress = Author

  AuthorName : Set
  AuthorName = Author

  aAuthorName : Lens Author AuthorName
  aAuthorName = mkLens' (λ x → x) (λ x → const x)

  U64 : Set
  U64 = ℕ

  Usize : Set
  Usize = ℕ

  HashValue : Set
  HashValue = Hash

  TX : Set
  TX = ByteString

  Instant : Set
  Instant = ℕ   -- TODO-2: should eventually be a time stamp

  -----------------
  -- Information --
  -----------------

  record BlockInfo : Set where
    constructor BlockInfo∙new
    field
      _biEpoch : Epoch
      _biRound : Round
      _biId    : HashValue
      -- This has more fields...
  open BlockInfo public
  unquoteDecl biEpoch   biRound   biId = mkLens (quote BlockInfo)
             (biEpoch ∷ biRound ∷ biId ∷ [])
  postulate instance enc-BlockInfo : Encoder BlockInfo

  BlockInfo-η : ∀{e1 e2 r1 r2 i1 i2} → e1 ≡ e2 → r1 ≡ r2 → i1 ≡ i2
              → BlockInfo∙new e1 r1 i1 ≡ BlockInfo∙new e2 r2 i2
  BlockInfo-η refl refl refl = refl

  record LedgerInfo : Set where
    constructor LedgerInfo∙new
    field
      _liCommitInfo        : BlockInfo
      _liConsensusDataHash : HashValue
  open LedgerInfo public
  unquoteDecl liCommitInfo   liConsensusDataHash = mkLens (quote LedgerInfo)
             (liCommitInfo ∷ liConsensusDataHash ∷ [])
  postulate instance enc-LedgerInfo : Encoder LedgerInfo
  postulate instance ws-LedgerInfo  : WithSig LedgerInfo

  LedgerInfo-η : ∀ {ci1 ci2 : BlockInfo} {cdh1 cdh2 : Hash}
             → ci1  ≡ ci2
             → cdh1 ≡ cdh2
             → (LedgerInfo∙new ci1 cdh1) ≡ (LedgerInfo∙new ci2 cdh2)
  LedgerInfo-η refl refl = refl

  record LedgerInfoWithSignatures : Set where
    constructor LedgerInfoWithSignatures∙new
    field
      _liwsLedgerInfo : LedgerInfo
      _liwsSignatures : KVMap Author Signature
  open LedgerInfoWithSignatures public
  unquoteDecl liwsLedgerInfo   liwsSignatures = mkLens (quote LedgerInfoWithSignatures)
             (liwsLedgerInfo ∷ liwsSignatures ∷ [])
  postulate instance enc-LedgerInfoWithSignatures : Encoder LedgerInfoWithSignatures

  -------------------
  -- Votes and QCs --
  -------------------

  record VoteData : Set where
    constructor VoteData∙new
    field
      _vdProposed : BlockInfo
      _vdParent   : BlockInfo
  open VoteData public
  unquoteDecl vdProposed   vdParent = mkLens (quote VoteData)
             (vdProposed ∷ vdParent ∷ [])
  postulate instance enc-VoteData : Encoder VoteData

  VoteData-η : ∀ {pr1 par1 pr2 par2 : BlockInfo} → pr1  ≡ pr2 → par1 ≡ par2
             → (VoteData∙new pr1 par1) ≡ (VoteData∙new pr2 par2)
  VoteData-η refl refl = refl

  -- DESIGN NOTE: The _vAuthor field is included only to facilitate lookup of the public key against
  -- which to verify the signature.  An alternative would be to use an index into the members of the
  -- epoch config, which would save message space and therefore bandwidth.
  record Vote : Set where
    constructor Vote∙new
    field
      _vVoteData         : VoteData
      _vAuthor           : Author
      _vLedgerInfo       : LedgerInfo
      _vSignature        : Signature
      _vTimeoutSignature : Maybe Signature
  open Vote public
  unquoteDecl vVoteData   vAuthor   vLedgerInfo   vSignature   vTimeoutSignature = mkLens (quote Vote)
             (vVoteData ∷ vAuthor ∷ vLedgerInfo ∷ vSignature ∷ vTimeoutSignature ∷ [])
  postulate instance enc-Vote     : Encoder Vote

  vParent : Lens Vote BlockInfo
  vParent = vVoteData ∙ vdParent

  vProposed : Lens Vote BlockInfo
  vProposed = vVoteData ∙ vdProposed

  vParentId : Lens Vote Hash
  vParentId = vVoteData ∙ vdParent ∙ biId

  vParentRound : Lens Vote Round
  vParentRound = vVoteData ∙ vdParent ∙ biRound

  vProposedId : Lens Vote Hash
  vProposedId = vVoteData ∙ vdProposed ∙ biId

  vEpoch : Lens Vote Epoch
  vEpoch = vVoteData ∙ vdProposed ∙ biEpoch

  vdRound : Lens VoteData Round
  vdRound = vdProposed ∙ biRound

  vRound : Lens Vote Round
  vRound = vVoteData ∙ vdRound

  record QuorumCert : Set where
    constructor QuorumCert∙new
    field
      _qcVoteData         : VoteData
      _qcSignedLedgerInfo : LedgerInfoWithSignatures
  open QuorumCert public
  unquoteDecl qcVoteData   qcSignedLedgerInfo = mkLens (quote QuorumCert)
             (qcVoteData ∷ qcSignedLedgerInfo ∷ [])
  postulate instance enc-QuorumCert : Encoder QuorumCert

  -- Because QuorumCert has an injective encoding (postulated, for now),
  -- we can use it to determine equality of QuorumCerts.
  _≟QC_ : (q1 q2 : QuorumCert) → Dec (q1 ≡ q2)
  _≟QC_ = ≡-Encoder enc-QuorumCert

  _QCBoolEq_ : QuorumCert → QuorumCert → Bool
  _QCBoolEq_ q1 q2 = does (q1 ≟QC q2)

  qcCertifiedBlock : Lens QuorumCert BlockInfo
  qcCertifiedBlock = qcVoteData ∙ vdProposed

  qcParentBlock : Lens QuorumCert BlockInfo
  qcParentBlock = qcVoteData ∙ vdParent

  qcCommitInfo : Lens QuorumCert BlockInfo
  qcCommitInfo = qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo

  -- Constructs a 'vote' that was gathered in a QC.
  rebuildVote : QuorumCert → Author × Signature → Vote
  rebuildVote qc (α , sig)
    = record { _vVoteData         = _qcVoteData qc
             ; _vAuthor           = α
             ; _vLedgerInfo       = qc ^∙ (qcSignedLedgerInfo ∙ liwsLedgerInfo)
             ; _vSignature        = sig
             ; _vTimeoutSignature = nothing -- Is this correct?  The original vote may have had a
                                            -- timeout signature, but we don't know.  Does it
                                            -- matter?
             }

  -- Two votes are equivalent if they are identical except they may differ on timeout signature
  _≈Vote_ : (v1 v2 : Vote) → Set
  v1 ≈Vote v2 = v2 ≡ record v1 { _vTimeoutSignature = _vTimeoutSignature v2 }

  qcVotesKV : QuorumCert → KVMap Author Signature
  qcVotesKV = _liwsSignatures ∘ _qcSignedLedgerInfo

  qcVotes : QuorumCert → List (Author × Signature)
  qcVotes qc = kvm-toList (qcVotesKV qc)

  qcCertifies : Lens QuorumCert  Hash
  qcCertifies = qcVoteData ∙ vdProposed ∙ biId

  qcRound : Lens QuorumCert Round
  qcRound = qcVoteData ∙ vdProposed ∙ biRound

  _qcCertifies : QuorumCert → Hash
  _qcCertifies q = q ^∙ qcCertifies

  _qcRound : QuorumCert → Round
  _qcRound q = q ^∙ qcRound

  ------------
  -- Blocks --
  ------------

  data BlockType : Set where
    Proposal : TX → Author → BlockType
    NilBlock : BlockType
    Genesis  : BlockType
  postulate instance enc-BlockType : Encoder BlockType

  record BlockData : Set where
    constructor BlockData∙new
    field
      _bdEpoch      : Epoch
      _bdRound      : Round
      -- QUESTION: How do we represent a block that extends the
      -- genesis block, which doesn't come with a QC.  Maybe the
      -- genesis block has an associated QC established for the epoch?
      _bdQuorumCert : QuorumCert
      _bdBlockType  : BlockType
  open BlockData public
  unquoteDecl bdEpoch   bdRound   bdQuorumCert   bdBlockType = mkLens (quote BlockData)
             (bdEpoch ∷ bdRound ∷ bdQuorumCert ∷ bdBlockType ∷ [])
  postulate instance enc-BlockData : Encoder BlockData

  bdParentId : Lens BlockData Hash
  bdParentId = bdQuorumCert ∙ qcVoteData ∙ vdParent ∙ biId

  -- This is the id of a block
  bdBlockId : Lens BlockData Hash
  bdBlockId = bdQuorumCert ∙ qcVoteData ∙ vdProposed ∙ biId

  bdAuthor : Lens BlockData (Maybe Author)
  bdAuthor = mkLens' g s
    where
    g : BlockData → Maybe Author
    g bd = case (bd ^∙ bdBlockType) of λ where
             (Proposal _ author) → just author
             _                   → nothing

    s : BlockData → Maybe Author → BlockData
    s bd nothing     = bd
    s bd (just auth) =
      bd & bdBlockType %~ λ where
        (Proposal tx _) → Proposal tx auth
        bdt → bdt

  -- The signature is a Maybe to allow us to use 'nothing' as the
  -- 'bSignature' when constructing a block to sign later.  Also,
  -- "nil" blocks are not signed because they are produced
  -- independently by different validators.  This is to enable
  -- committing after an epoch-changing command is processed: we
  -- cannot add more commands, but we need to add some quorum
  -- certificates in order to commit the epoch-changing command.
  record Block : Set where
    constructor Block∙new
    field
      _bId        : HashValue
      _bBlockData : BlockData
      _bSignature : Maybe Signature
  open Block public
  unquoteDecl bId   bBlockData   bSignature = mkLens (quote Block)
             (bId ∷ bBlockData ∷ bSignature ∷ [])

  postulate instance enc : Encoder Block

  bQuorumCert : Lens Block QuorumCert
  bQuorumCert  = bBlockData ∙ bdQuorumCert

  bRound : Lens Block Round
  bRound =  bBlockData ∙ bdRound

  bAuthor : Lens Block (Maybe Author)
  bAuthor = bBlockData ∙ bdAuthor

  bParentId : Lens Block HashValue
  bParentId = bQuorumCert ∙ qcCertifiedBlock ∙ biId

  bEpoch : Lens Block Epoch
  bEpoch = bBlockData ∙ bdEpoch

  record BlockRetriever : Set where
    constructor BlockRetriever∙new
    field
      _brDeadline      : Instant
      _brPreferredPeer : Author
  open BlockRetriever public
  unquoteDecl brDeadline   brPreferredPeer = mkLens (quote BlockRetriever)
             (brDeadline ∷ brPreferredPeer ∷ [])

  record VoteProposal : Set where
    constructor VoteProposal∙new
    field
      -- _vpAccumulatorExtensionProof : AccumulatorExtensionProof
      _vpBlock : Block
      -- _vpNextEpochState : Maybe EpochState
  open VoteProposal public
  unquoteDecl  vpBlock = mkLens (quote VoteProposal)
              (vpBlock ∷ [])

  record MaybeSignedVoteProposal : Set where
    constructor MaybeSignedVoteProposal∙new
    field
      _msvpVoteProposal : VoteProposal
  open MaybeSignedVoteProposal public
  unquoteDecl  msvpVoteProposal = mkLens (quote MaybeSignedVoteProposal)
              (msvpVoteProposal ∷ [])

  record SyncInfo : Set where
    constructor mkSyncInfo -- Bare constructor to enable pattern matching against SyncInfo; "smart"
                           -- constructor SyncInfo∙new is below
    field
      _siHighestQuorumCert  : QuorumCert
      _sixxxHighestCommitCert  : Maybe QuorumCert
      -- _siHighestTimeoutCert : Maybe TimeoutCert -- Not used yet.
  open SyncInfo public
  -- Note that we do not automatically derive a lens for siHighestCommitCert;
  -- it is defined manually below.
  unquoteDecl siHighestQuorumCert   sixxxHighestCommitCert = mkLens (quote SyncInfo)
             (siHighestQuorumCert ∷ sixxxHighestCommitCert ∷ [])
  postulate instance enc-SyncInfo : Encoder SyncInfo

  SyncInfo∙new : QuorumCert → QuorumCert → SyncInfo
  SyncInfo∙new highestQuorumCert highestCommitCert =
    record { _siHighestQuorumCert    = highestQuorumCert
           ; _sixxxHighestCommitCert = if highestQuorumCert QCBoolEq highestCommitCert
                                       then nothing else (just highestCommitCert) }

  siHighestCommitCert : Lens SyncInfo QuorumCert
  siHighestCommitCert =
    mkLens' (λ x → fromMaybe (x ^∙ siHighestQuorumCert) (x ^∙ sixxxHighestCommitCert))
            (λ x si → record x { _sixxxHighestCommitCert = just si })

  siHighestCommitRound : Lens SyncInfo Round
  siHighestCommitRound = siHighestCommitCert ∙ qcCommitInfo ∙ biRound

  ----------------------
  -- Network Messages --
  ----------------------

  record ProposalMsg : Set where
    constructor ProposalMsg∙new
    field
      _pmProposal : Block
      _pmSyncInfo : SyncInfo
  open ProposalMsg public
  unquoteDecl pmProposal   pmSyncInfo = mkLens (quote ProposalMsg)
             (pmProposal ∷ pmSyncInfo ∷ [])
  postulate instance enc-ProposalMsg : Encoder ProposalMsg

  pmProposer : Lens ProposalMsg (Maybe Author)
  pmProposer = pmProposal ∙ bAuthor

  record VoteMsg : Set where
    constructor  VoteMsg∙new
    field
      _vmVote     : Vote
      _vmSyncInfo : SyncInfo
  open VoteMsg public
  unquoteDecl vmVote   vmSyncInfo = mkLens (quote VoteMsg)
             (vmVote ∷ vmSyncInfo ∷ [])
  postulate instance enc-VoteMsg : Encoder VoteMsg

  vmProposed : Lens VoteMsg BlockInfo
  vmProposed = vmVote ∙ vVoteData ∙ vdProposed

  vmParent : Lens VoteMsg BlockInfo
  vmParent = vmVote ∙ vVoteData ∙ vdParent


  -- This is a notification of a commit.  It may not be explicitly included in an implementation,
  -- but we need something to be able to express correctness conditions.  It will
  -- probably have something different in it, but will serve the purpose for now.
  record CommitMsg : Set where
    constructor CommitMsg∙new
    field
      _cmEpoch   : Epoch
      _cmAuthor  : NodeId
      _cmRound   : Round
      _cmCert    : QuorumCert  -- We assume for now that a CommitMsg contains the QuorumCert of the head of the 3-chain
      _cmSigMB   : Maybe Signature
  open CommitMsg public
  unquoteDecl cmEpoch   cmAuthor   cmRound   cmCert   cmSigMB = mkLens (quote CommitMsg)
             (cmEpoch ∷ cmAuthor ∷ cmRound ∷ cmCert ∷ cmSigMB ∷ [])
  postulate instance enc-CommitMsg : Encoder CommitMsg

  record LastVoteInfo : Set where
    constructor LastVoteInfo∙new
    field
      _lviLiDigest  : HashValue
      _lviRound     : Round
      _lviIsTimeout : Bool
  open LastVoteInfo public

  record Timeout : Set where
    constructor Timeout∙new
    field
      _toEpoch : Epoch
      _toRound : Round
  open Timeout public
  unquoteDecl toEpoch   toRound = mkLens (quote Timeout)
             (toEpoch ∷ toRound ∷ [])
  postulate instance enc-Timeout : Encoder Timeout

  record TimeoutCertificate : Set where
    constructor mkTimeoutCertificate
    field
      _tcTimeout    : Timeout
      _tcSignatures : KVMap Author Signature
  open TimeoutCertificate public
  unquoteDecl tcTimeout   tcSignatures = mkLens (quote TimeoutCertificate)
             (tcTimeout ∷ tcSignatures ∷ [])

  TimeoutCertificate∙new : Timeout → TimeoutCertificate
  TimeoutCertificate∙new to = mkTimeoutCertificate to KVMap.empty

  -- IMPL-DIFF : only a getter in haskell
  tcEpoch : Lens TimeoutCertificate Epoch
  tcEpoch = tcTimeout ∙ toEpoch

  -- IMPL-DIFF : only a getter in haskell
  tcRound : Lens TimeoutCertificate Round
  tcRound = tcTimeout ∙ toRound

  record PendingVotes : Set where
    constructor PendingVotes∙new
    field
      _pvLiDigestToVotes   : KVMap HashValue LedgerInfoWithSignatures
      _pvMaybePartialTC    : Maybe TimeoutCertificate
      _pvAuthorToVote      : KVMap Author Vote
  open PendingVotes public
  unquoteDecl pvLiDigestToVotes   pvMaybePartialTC   pvAuthorToVote = mkLens (quote PendingVotes)
             (pvLiDigestToVotes ∷ pvMaybePartialTC ∷ pvAuthorToVote ∷ [])

  -- Note: this is a placeholder.
  -- We are not concerned for now with executing transactions, just ordering/committing them.
  -- This is outdated (see comment at top).
  data StateComputeResult : Set where
    stateComputeResult : StateComputeResult

  record ExecutedBlock : Set where
    constructor ExecutedBlock∙new
    field
      _ebBlock  : Block
      _ebOutput : StateComputeResult
  open ExecutedBlock public
  unquoteDecl ebBlock   ebOutput = mkLens (quote ExecutedBlock)
             (ebBlock ∷ ebOutput ∷ [])

  ebId : Lens ExecutedBlock HashValue
  ebId = ebBlock ∙ bId

  ebQuorumCert : Lens ExecutedBlock QuorumCert
  ebQuorumCert = ebBlock ∙ bQuorumCert

  ebParentId : Lens ExecutedBlock HashValue
  ebParentId = ebQuorumCert ∙ qcCertifiedBlock ∙ biId

  ebRound : Lens ExecutedBlock Round
  ebRound = ebBlock ∙ bRound

-- ------------------------------------------------------------------------------

  record LinkableBlock : Set where
    constructor LinkableBlock∙new
    field
      _lbExecutedBlock : ExecutedBlock
      -- _lbChildren      : Set HashValue
  open LinkableBlock public
  unquoteDecl lbExecutedBlock = mkLens (quote LinkableBlock)
             (lbExecutedBlock ∷ [])

  lbId : Lens LinkableBlock HashValue
  lbId = lbExecutedBlock ∙ ebId

-- ------------------------------------------------------------------------------

  -- Note BlockTree and BlockStore are defined in EpochDep.agda as they depend on an EpochConfig

  record SafetyData : Set where
    constructor SafetyData∙new
    field
      _sdEpoch          : Epoch
      _sdLastVotedRound : Round
      _sdPreferredRound : Round
      _sdLastVote       : Maybe Vote
  open SafetyData public
  unquoteDecl sdEpoch sdLastVotedRound sdPreferredRound sdLastVote =
    mkLens (quote SafetyData)
    (sdEpoch ∷ sdLastVotedRound ∷ sdPreferredRound ∷ sdLastVote ∷  [])

  record PersistentSafetyStorage : Set where
    constructor PersistentSafetyStorage∙new
    field
      _pssSafetyData : SafetyData
      _pssAuthor     : Author
      -- _pssWaypoint : Waypoint
  open PersistentSafetyStorage public
  unquoteDecl pssSafetyData pssAuthor = mkLens (quote PersistentSafetyStorage)
    (pssSafetyData ∷ pssAuthor ∷ [])

  record ValidatorSigner : Set where
    constructor ValidatorSigner∙new
    field
      _vsAuthor     : AccountAddress
      _vsPrivateKey : SK      -- Note that the SystemModel doesn't
                              -- allow one node to examine another's
                              -- state, so we don't model someone being
                              -- able to impersonate someone else unless
                              -- PK is "dishonest", which models the
                              -- possibility that the corresponding secret
                              -- key may have been leaked.
  open ValidatorSigner public
  unquoteDecl  vsAuthor = mkLens (quote ValidatorSigner)
              (vsAuthor ∷ [])

  record ValidatorConfig : Set where
    constructor ValidatorConfig∙new
    field
     _vcConsensusPublicKey : PK
  open ValidatorConfig public
  unquoteDecl vcConsensusPublicKey = mkLens (quote ValidatorConfig)
    (vcConsensusPublicKey ∷ [])

  record ValidatorInfo : Set where
    constructor ValidatorInfo∙new
    field
      -- _viAccountAddress       : AccountAddress
      -- _viConsensusVotingPower : Int -- TODO-2: Each validator has one vote. Generalize later.
      _viConfig : ValidatorConfig
  open ValidatorInfo public

  record ValidatorConsensusInfo : Set where
    constructor ValidatorConsensusInfo∙new
    field
     _vciPublicKey   : PK
     _vciVotingPower : U64
  open ValidatorConsensusInfo public
  unquoteDecl vciPublicKey   vciVotingPower = mkLens (quote ValidatorConsensusInfo)
             (vciPublicKey ∷ vciVotingPower ∷ [])

  record ProposerElection : Set where
    constructor ProposerElection∙new
    -- field
      -- :peProposers : Set Author
      -- :peObmLeaderOfRound : LeaderOfRoundFn
      -- :peObmNodesInORder  : NodesInOrder
  open ProposerElection

  record ValidatorVerifier : Set where
    constructor ValidatorVerifier∙new
    field
      _vvAddressToValidatorInfo : (KVMap AccountAddress ValidatorConsensusInfo)
      _vvQuorumVotingPower      : ℕ  -- TODO-2: see above; for now, this is QuorumSize
      -- :vvTotalVotingPower    : ℕ  -- TODO-2: see above; for now, this is number of peers in EpochConfig
  open ValidatorVerifier public
  unquoteDecl vvAddressToValidatorInfo   vvQuorumVotingPower = mkLens  (quote ValidatorVerifier)
             (vvAddressToValidatorInfo ∷ vvQuorumVotingPower ∷ [])

  record SafetyRules : Set where
    constructor SafetyRules∙new
    field
      _srPersistentStorage  : PersistentSafetyStorage
      _srExecutionPublicKey : Maybe PK
      _srValidatorSigner    : Maybe ValidatorSigner
  open SafetyRules public
  unquoteDecl srPersistentStorage   srExecutionPublicKey   srValidatorSigner = mkLens (quote SafetyRules)
             (srPersistentStorage ∷ srExecutionPublicKey ∷ srValidatorSigner ∷ [])

  data VoteReceptionResult : Set where
    QCVoteAdded           : U64 →                VoteReceptionResult
    TCVoteAdded           : U64 →                VoteReceptionResult
    DuplicateVote         :                      VoteReceptionResult
    EquivocateVote        :                      VoteReceptionResult
    NewQuorumCertificate  : QuorumCert →         VoteReceptionResult
    NewTimeoutCertificate : TimeoutCertificate → VoteReceptionResult
    UnexpectedRound       : Round → Round →      VoteReceptionResult
    VRR_TODO              :                      VoteReceptionResult

  data VerifyError : Set where
    UnknownAuthor        : AuthorName →    VerifyError
    TooLittleVotingPower : U64 → U64 →     VerifyError
    TooManySignatures    : Usize → Usize → VerifyError
    InvalidSignature     :                 VerifyError
