{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.Encode
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.KVMap as KVMap

open import Optics.All

open import Data.String using (String)

-- Defines the types that /DO NOT/ depend on an epoch config.
-- TODO-3: update types to reflect more recent version of LibraBFT.  This is
-- a substantial undertaking that should probably be led by someone who can
-- access our internal implementation.
module LibraBFT.Impl.Consensus.Types.EpochIndep where

  open import LibraBFT.Abstract.Types public

  -- Below here is incremental progress towards something
  -- that will eventually mirror the types in LBFT.Consensus.Types
  -- that /DO NOT/ depend on the set of active authors
  -- or safety rules, which we call the /EpochConfig/.

  Author : Set
  Author = NodeId

  AccountAddress : Set
  AccountAddress = Author

  _≟AccountAddress_ : (a₁ a₂ : AccountAddress) → Dec (a₁ ≡ a₂)
  _≟AccountAddress_ = _≟_

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
    constructor mkBlockInfo
    field
      ₋biEpoch : EpochId
      ₋biRound : Round
      ₋biId    : HashValue
      -- This has more fields...
  open BlockInfo public
  unquoteDecl biEpoch   biRound   biId = mkLens (quote BlockInfo)
             (biEpoch ∷ biRound ∷ biId ∷ [])
  postulate instance enc-BlockInfo : Encoder BlockInfo

  BlockInfo-η : ∀{e1 e2 r1 r2 i1 i2} → e1 ≡ e2 → r1 ≡ r2 → i1 ≡ i2
              → mkBlockInfo e1 r1 i1 ≡ mkBlockInfo e2 r2 i2
  BlockInfo-η refl refl refl = refl

  record LedgerInfo : Set where
    constructor mkLedgerInfo
    field
      ₋liCommitInfo        : BlockInfo
      ₋liConsensusDataHash : HashValue
  open LedgerInfo public
  unquoteDecl liCommitInfo   liConsensusDataHash = mkLens (quote LedgerInfo)
             (liCommitInfo ∷ liConsensusDataHash ∷ [])
  postulate instance enc-LedgerInfo : Encoder LedgerInfo

  LedgerInfo-η : ∀ {ci1 ci2 : BlockInfo} {cdh1 cdh2 : Hash}
             → ci1  ≡ ci2
             → cdh1 ≡ cdh2
             → (mkLedgerInfo ci1 cdh1) ≡ (mkLedgerInfo ci2 cdh2)
  LedgerInfo-η refl refl = refl

  record LedgerInfoWithSignatures : Set where
    constructor mkLedgerInfoWithSignatures
    field
      ₋liwsLedgerInfo : LedgerInfo
      ₋liwsSignatures : KVMap Author Signature
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
      ₋vdProposed : BlockInfo
      ₋vdParent   : BlockInfo
  open VoteData public
  unquoteDecl vdProposed   vdParent = mkLens (quote VoteData)
             (vdProposed ∷ vdParent ∷ [])
  postulate instance enc-VoteData : Encoder VoteData

  VoteData-η : ∀ {pr1 par1 pr2 par2 : BlockInfo} → pr1  ≡ pr2 → par1 ≡ par2
             → (mkVoteData pr1 par1) ≡ (mkVoteData pr2 par2)
  VoteData-η refl refl = refl

  -- DESIGN NOTE: The ₋vAuthor field is included only to facilitate lookup of the public key against
  -- which to verify the signature.  An alternative would be to use an index into the members of the
  -- epoch config, which would save message space and therefore bandwidth.

  record Vote : Set where
    constructor mkVote
    field
      ₋vVoteData         : VoteData
      ₋vAuthor           : Author
      ₋vLedgerInfo       : LedgerInfo
      ₋vSignature        : Signature
      ₋vTimeoutSignature : Maybe Signature
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

  vEpoch : Lens Vote EpochId
  vEpoch = vVoteData ∙ vdProposed ∙ biEpoch

  vRound : Lens Vote Round
  vRound = vVoteData ∙ vdProposed ∙ biRound

  record QuorumCert : Set where
    constructor mkQuorumCert
    field
      ₋qcVoteData         : VoteData
      ₋qcSignedLedgerInfo : LedgerInfoWithSignatures
  open QuorumCert public
  unquoteDecl qcVoteData   qcSignedLedgerInfo = mkLens (quote QuorumCert)
             (qcVoteData ∷ qcSignedLedgerInfo ∷ [])
  postulate instance enc-QuorumCert : Encoder QuorumCert

  qcCertifiedBlock : Lens QuorumCert BlockInfo
  qcCertifiedBlock = qcVoteData ∙ vdProposed

  -- Constructs a 'vote' that was gathered in a QC.
  rebuildVote : QuorumCert → Author × Signature → Vote
  rebuildVote qc (α , sig)
    = record { ₋vVoteData         = ₋qcVoteData qc
             ; ₋vAuthor           = α
             ; ₋vLedgerInfo       = qc ^∙ (qcSignedLedgerInfo ∙ liwsLedgerInfo)
             ; ₋vSignature        = sig
             ; ₋vTimeoutSignature = nothing -- Is this correct?  The original vote may have had a
                                            -- timeout signature, but we don't know.  Does it
                                            -- matter?
             }

  record _≈Vote_ (v1 v2 : Vote) : Set where
    constructor equivVotes
    field
      sameProposed : v1 ^∙ vProposedId ≡ v2 ^∙ vProposedId
      sameRound    : v1 ^∙ vRound      ≡ v2 ^∙ vRound
      sameAuthor   : v1 ^∙ vAuthor     ≡ v2 ^∙ vAuthor
  open _≈Vote_ public

  qcVotesKV : QuorumCert → KVMap Author Signature
  qcVotesKV = ₋liwsSignatures ∘ ₋qcSignedLedgerInfo

  qcVotes : QuorumCert → List (Author × Signature)
  qcVotes qc = kvm-toList (qcVotesKV qc)

  qcCertifies : Lens QuorumCert  Hash
  qcCertifies = qcVoteData ∙ vdProposed ∙ biId

  qcRound : Lens QuorumCert Round
  qcRound = qcVoteData ∙ vdProposed ∙ biRound

  ₋qcCertifies : QuorumCert → Hash
  ₋qcCertifies q = q ^∙ qcCertifies

  ₋qcRound : QuorumCert → Round
  ₋qcRound q = q ^∙ qcRound

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
      ₋bdEpoch      : EpochId
      ₋bdRound      : Round
      -- QUESTION: How do we represent a block that extends the
      -- genesis block, which doesn't come with a QC.  Maybe the
      -- genesis block has an associated QC established for the epoch?
      ₋bdQuorumCert : QuorumCert
      ₋bdBlockType  : BlockType
  open BlockData public
  unquoteDecl bdEpoch   bdRound   bdQuorumCert   bdBlockType = mkLens (quote BlockData)
             (bdEpoch ∷ bdRound ∷ bdQuorumCert ∷ bdBlockType ∷ [])
  postulate instance enc-BlockData : Encoder BlockData

  bdParentId : Lens BlockData Hash
  bdParentId = bdQuorumCert ∙ qcVoteData ∙ vdParent ∙ biId

  -- This is the id of a block
  bdBlockId : Lens BlockData Hash
  bdBlockId = bdQuorumCert ∙ qcVoteData ∙ vdProposed ∙ biId

  -- The signature is a Maybe to allow us to use 'nothing' as the
  -- 'bSignature' when constructing a block to sign later.  Also,
  -- "nil" blocks are not signed because they are produced
  -- independently by different validators.  This is to enable
  -- committing after an epoch-changing command is processed: we
  -- cannot add more commands, but we need to add some quorum
  -- certificates in order to commit the epoch-changing command.
  record Block : Set where
    constructor mkBlock
    field
      ₋bId        : HashValue
      ₋bBlockData : BlockData
      ₋bSignature : Maybe Signature
  open Block public
  unquoteDecl bId   bBlockData   bSignature = mkLens (quote Block)
             (bId ∷ bBlockData ∷ bSignature ∷ [])

  postulate instance enc : Encoder Block

  bQuorumCert : Lens Block QuorumCert
  bQuorumCert  = bBlockData ∙ bdQuorumCert

  bRound : Lens Block Round
  bRound =  bBlockData ∙ bdRound

  record SyncInfo : Set where
    constructor mkSyncInfo
    field
      ₋siHighestQuorumCert  : QuorumCert
      ₋siHighestCommitCert  : QuorumCert
      -- ₋siHighestTimeoutCert : Mabe TimeoutCert -- Not used yet.
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
      ₋pmProposal : Block
      ₋pmSyncInfo : SyncInfo
  open ProposalMsg public
  unquoteDecl pmProposal   pmSyncInfo = mkLens (quote ProposalMsg)
             (pmProposal ∷ pmSyncInfo ∷ [])
  postulate instance enc-ProposalMsg : Encoder ProposalMsg

  record VoteMsg : Set where
    constructor  mkVoteMsg
    field
      ₋vmVote     : Vote
      ₋vmSyncInfo : SyncInfo
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
    constructor mkCommitMsg
    field
      ₋cEpochId : EpochId
      ₋cAuthor  : NodeId
      ₋cRound   : Round
      ₋cCert    : QuorumCert  -- We assume for now that a CommitMsg contains the QuorumCert of the head of the 3-chain
      ₋cSigMB   : Maybe Signature
  open CommitMsg public
  unquoteDecl cEpochId   cAuthor   cRound   cCert   cSigMB = mkLens (quote CommitMsg)
             (cEpochId ∷ cAuthor ∷ cRound ∷ cCert ∷ cSigMB ∷ [])
  postulate instance enc-CommitMsg : Encoder CommitMsg

  record LastVoteInfo : Set where
    constructor LastVoteInfo₋new
    field
      ₋lviLiDigest  : HashValue
      ₋lviRound     : Round
      ₋lviIsTimeout : Bool
  open LastVoteInfo public

  record PendingVotes : Set where
    constructor mkPendingVotes
    field
      ₋pvLiDigestToVotes       : KVMap HashValue LedgerInfoWithSignatures
      -- ₋pvRoundToTC          : KVMap Round TimeoutCertificate
      ₋pvAuthorToLastVotedInfo : KVMap Author LastVoteInfo
  open PendingVotes public

  data ProcessedVMOutput : Set where      -- Note: this is a placeholder.  We are not concerned for now with
    processedVMOutput : ProcessedVMOutput -- executing transactions, just ordering/committing them.
                                          -- Furthermore, this is outdated (see comment at top).

  record ExecutedBlock : Set where
    constructor ExecutedBlock₋new
    field
      ₋ebBlock  : Block
      ₋ebOutput : ProcessedVMOutput
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
    constructor LinkableBlock₋new
    field
      ₋lbExecutedBlock : ExecutedBlock
      -- ₋lbChildren      : Set HashValue
  open LinkableBlock public
  unquoteDecl lbExecutedBlock = mkLens (quote LinkableBlock)
             (lbExecutedBlock ∷ [])

  lbId : Lens LinkableBlock HashValue
  lbId = lbExecutedBlock ∙ ebId

-- ------------------------------------------------------------------------------

  -- Note BlockTree and BlockStore are defined in EpochDep.agda as they depend on an EpochConfig

  record PersistentStorage : Set where
    constructor mkPersistentStorage
    field
      :psEpoch          : EpochId
      :psLastVotedRound : Round
      -- :psPreferredRound : Round
  open PersistentStorage public
  unquoteDecl psEpoch psLastVotedRound = mkLens (quote PersistentStorage)
    (psEpoch ∷ psLastVotedRound ∷ [])

  record ValidatorSigner : Set where
    constructor mkValidatorSigner
    field
      :vsAuthor     : AccountAddress
      -- :vsPublicKey  : PK
      -- :vsPrivateKey : SK   -- Note that the SystemModel doesn't
                              -- allow one node to examine another's
                              -- state, so we don't model someone being
                              -- able to impersonate someone else unless
                              -- PK is "dishonest", which models the
                              -- possibility that the corresponding secret
                              -- key may have been leaked.
  open ValidatorSigner public

  record ValidatorInfo : Set where
    constructor mkValidatorInfo
    field
      :viPublicKey   : PK
      -- :viVotingPower : Int  -- TODO-2: For now we consider each validator to have one
                               --         vote.  Generalize later.
  open ValidatorInfo public

  record ValidatorVerifier : Set where
    constructor mkValidatorVerifier
    field
      :vvAddressToValidatorInfo : (KVMap AccountAddress ValidatorInfo)
      :vvQuorumVotingPower      : ℕ  -- TODO-2: see above; for now, this is QuorumSize
      -- :vvTotalVotingPower    : ℕ  -- TODO-2: see above; for now, this is number of peers in EpochConfig
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

  data Output : Set where
    BroadcastProposal : ProposalMsg           → Output
    LogErr            : String                → Output
    -- LogInfo           : InfoLog a          → Output
    SendVote          : VoteMsg → List Author → Output
  open Output public
