{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap            as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.OBM.Rust.RustTypes
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

  HashValue : Set
  HashValue = Hash

  TX : Set
  TX = ByteString

  Instant : Set
  Instant = ℕ   -- TODO-2: should eventually be a time stamp

  postulate -- TODO-1: implement/prove PK equality
    _≟-PK_ : (pk1 pk2 : PK) → Dec (pk1 ≡ pk2)
  instance
    Eq-PK : Eq PK
    Eq._≟_ Eq-PK = _≟-PK_

  -- LBFT-OBM-DIFF: We do not have world state.  We just count the Epoch/Round as the version.
  record Version : Set where
    constructor Version∙new
    field
      _vVE : Epoch
      _vVR : Round
  open Version public
  postulate instance enc-Version : Encoder Version

  postulate -- TODO-1: implement/prove Version equality
    _≟-Version_ : (v1 v2 : Version) → Dec (v1 ≡ v2)
  instance
    Eq-Version : Eq Version
    Eq._≟_ Eq-Version = _≟-Version_

  _≤-Version_ : Version → Version → Set
  v1 ≤-Version v2 = _vVE v1 < _vVE v2
                  ⊎ _vVE v1 ≡ _vVE v2 × _vVR v1 ≤ _vVR v2

  _≤?-Version_ : (v1 v2 : Version) → Dec (v1 ≤-Version v2)
  v1 ≤?-Version v2
     with _vVE v1 <? _vVE v2
  ...| yes prf = yes (inj₁ prf)
  ...| no  ege
     with _vVE v1 ≟ _vVE v2
  ...| no  rneq = no (⊥-elim ∘ λ { (inj₁ x) → ege x
                                 ; (inj₂ (x , _)) → rneq x })
  ...| yes refl
     with _vVR v1 ≤? _vVR v2
  ...| yes rleq = yes (inj₂ (refl , rleq))
  ...| no  rgt  = no (⊥-elim ∘ λ { (inj₁ x) → ege x
                                 ; (inj₂ (_ , x)) → rgt x })

  _<-Version_ : Version → Version → Set
  v1 <-Version v2 = _vVE v1 < _vVE v2
                  ⊎ _vVE v1 ≡ _vVE v2 × _vVR v1 < _vVR v2

  _<?-Version_ : (v1 v2 : Version) → Dec (v1 <-Version v2)
  v1 <?-Version v2
     with _vVE v1 <? _vVE v2
  ...| yes prf = yes (inj₁ prf)
  ...| no  ege
     with _vVE v1 ≟ _vVE v2
  ...| no  rneq = no (⊥-elim ∘ λ { (inj₁ x) → ege x
                                 ; (inj₂ (x , _)) → rneq x })
  ...| yes refl
     with _vVR v1 <? _vVR v2
  ...| yes rleq = yes (inj₂ (refl , rleq))
  ...| no  rgt  = no (⊥-elim ∘ λ { (inj₁ x) → ege x
                                 ; (inj₂ (_ , x)) → rgt x })

  -----------------
  -- Information --
  -----------------

  record ValidatorConsensusInfo : Set where
    constructor ValidatorConsensusInfo∙new
    field
     _vciPublicKey   : PK
     _vciVotingPower : U64
  open ValidatorConsensusInfo public
  unquoteDecl vciPublicKey   vciVotingPower = mkLens (quote ValidatorConsensusInfo)
             (vciPublicKey ∷ vciVotingPower ∷ [])

  record ValidatorVerifier : Set where
    constructor ValidatorVerifier∙new
    field
      _vvAddressToValidatorInfo : (KVMap AccountAddress ValidatorConsensusInfo)
      _vvQuorumVotingPower      : ℕ  -- TODO-2: see above; for now, this is QuorumSize
      -- :vvTotalVotingPower    : ℕ  -- TODO-2: see above; for now, this is number of peers in EpochConfig
  open ValidatorVerifier public
  unquoteDecl vvAddressToValidatorInfo   vvQuorumVotingPower = mkLens (quote ValidatorVerifier)
             (vvAddressToValidatorInfo ∷ vvQuorumVotingPower ∷ [])

  record EpochState : Set where
    constructor EpochState∙new
    field
      _esEpoch    : Epoch
      _esVerifier : ValidatorVerifier
  open EpochState public
  unquoteDecl esEpoch   esVerifier = mkLens (quote EpochState)
             (esEpoch ∷ esVerifier ∷ [])

  record Ledger2WaypointConverter : Set where
    constructor mkLedger2WaypointConverter
    field
      _l2wcEpoch          : Epoch
      _l2wcRootHash       : HashValue
      _l2wcVersion        : Version
    --_l2wcTimestamp      : Instant
      _l2wcNextEpochState : Maybe EpochState
  open Ledger2WaypointConverter public
  unquoteDecl l2wcEpoch   2wcRootHash   2wcVersion
              {-l2wcTimestamp-} l2wcNextEpochState = mkLens (quote Ledger2WaypointConverter)
             (l2wcEpoch ∷ 2wcRootHash ∷ 2wcVersion ∷
              {-l2wcTimestamp-} l2wcNextEpochState ∷ [])

  postulate -- one valid assumption, one that can be proved using it
    instance
      Enc-EpochState   : Encoder EpochState
      Enc-EpochStateMB : Encoder (Maybe EpochState)  -- TODO-1: make combinator to build this

  record BlockInfo : Set where
    constructor BlockInfo∙new
    field
      _biEpoch           : Epoch
      _biRound           : Round
      _biId              : HashValue
      _biExecutedStateId : HashValue -- aka liTransactionAccumulatorHash
      _biVersion         : Version
      --, _biTimestamp       :: Instant
      _biNextEpochState  : Maybe EpochState
  open BlockInfo public
  unquoteDecl biEpoch   biRound   biId   biExecutedStateId   biVersion   biNextEpochState = mkLens (quote BlockInfo)
             (biEpoch ∷ biRound ∷ biId ∷ biExecutedStateId ∷ biVersion ∷ biNextEpochState ∷ [])
  postulate instance enc-BlockInfo : Encoder BlockInfo

  postulate
    _≟-BlockInfo_ : (bi1 bi2 : BlockInfo) → Dec (bi1 ≡ bi2)

  instance
    Eq-BlockInfo : Eq BlockInfo
    Eq._≟_ Eq-BlockInfo = _≟-BlockInfo_

  BlockInfo-η : ∀{e1 e2 r1 r2 i1 i2 x1 x2 v1 v2 n1 n2}
              → e1 ≡ e2 → r1 ≡ r2 → i1 ≡ i2 → x1 ≡ x2 → v1 ≡ v2 → n1 ≡ n2
              → BlockInfo∙new e1 r1 i1 x1 v1 n1 ≡ BlockInfo∙new e2 r2 i2 x2 v2 n2
  BlockInfo-η refl refl refl refl refl refl = refl

  instance
    Eq-ByteString : Eq ByteString
    Eq._≟_ Eq-ByteString = _≟ByteString_

{-
  _≟BlockInfo_ : (b₁ b₂ : BlockInfo) → Dec (b₁ ≡ b₂)
  l ≟BlockInfo r with ((l ^∙ biEpoch) ≟ (r ^∙ biEpoch))
  ...| no  no-e = no  λ where refl → no-e refl
  ...| yes refl with ((l ^∙ biRound)  ≟ (r ^∙ biRound))
  ...| no  no-r = no  λ where refl → no-r refl
  ...| yes refl with ((l ^∙ biId)     ≟ (r ^∙ biId))
  ...| no  no-i = no  λ where refl → no-i refl
  ...| yes refl = yes refl

  instance
    Eq-BlockInfo : Eq BlockInfo
    Eq._≟_ Eq-BlockInfo = _≟BlockInfo_

  BlockInfo-η : ∀{e1 e2 r1 r2 i1 i2} → e1 ≡ e2 → r1 ≡ r2 → i1 ≡ i2
              → BlockInfo∙new e1 r1 i1 ≡ BlockInfo∙new e2 r2 i2
  BlockInfo-η refl refl refl = refl
-}

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

  -- GETTER only in Haskell
  liEpoch : Lens LedgerInfo Epoch
  liEpoch = liCommitInfo ∙ biEpoch

  -- GETTER only in Haskell
  liConsensusBlockId : Lens LedgerInfo HashValue
  liConsensusBlockId = liCommitInfo ∙ biId

  -- GETTER only in Haskell
  liTransactionAccumulatorHash : Lens LedgerInfo HashValue
  liTransactionAccumulatorHash = liCommitInfo ∙ biExecutedStateId

  -- GETTER only in Haskell
  liVersion : Lens LedgerInfo Version
  liVersion = liCommitInfo ∙ biVersion

  -- GETTER only in Haskell
  liNextEpochState : Lens LedgerInfo (Maybe EpochState)
  liNextEpochState = mkLens' g s
   where
    g : LedgerInfo → Maybe EpochState
    g = (_^∙ liCommitInfo ∙ biNextEpochState)
    s : LedgerInfo → Maybe EpochState → LedgerInfo
    s l _ = l -- TODO-1 : cannot be done: need a way to defined only getters

  -- GETTER only in Haskell
  liEndsEpoch : Lens LedgerInfo Bool
  liEndsEpoch = mkLens' g s
   where
    g : LedgerInfo → Bool
    g = is-just ∘ (_^∙ liNextEpochState)
    s : LedgerInfo → Bool → LedgerInfo
    s l _ = l -- TODO-1 : cannot be done: need a way to defined only getters

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

  -- GETTER only in Haskell
  liwsVersion : Lens LedgerInfoWithSignatures Version
  liwsVersion = liwsLedgerInfo ∙ liVersion

  -- GETTER only in Haskell
  liwsNextEpochState : Lens LedgerInfoWithSignatures (Maybe EpochState)
  liwsNextEpochState = liwsLedgerInfo ∙ liNextEpochState

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

  -- not defined in Haskell
  vParent : Lens Vote BlockInfo
  vParent = vVoteData ∙ vdParent

  -- not defined in Haskell
  vProposed : Lens Vote BlockInfo
  vProposed = vVoteData ∙ vdProposed

  -- not defined in Haskell
  vParentId : Lens Vote Hash
  vParentId = vVoteData ∙ vdParent ∙ biId

  -- not defined in Haskell
  vParentRound : Lens Vote Round
  vParentRound = vVoteData ∙ vdParent ∙ biRound

  -- not defined in Haskell
  vProposedId : Lens Vote Hash
  vProposedId = vVoteData ∙ vdProposed ∙ biId

  -- getter only in Haskell
  vEpoch : Lens Vote Epoch
  vEpoch = vVoteData ∙ vdProposed ∙ biEpoch

  -- getter only in Haskell
  vRound : Lens Vote Round
  vRound = vVoteData ∙ vdProposed ∙ biRound

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

  -- getter only in Haskell
  qcCertifiedBlock : Lens QuorumCert BlockInfo
  qcCertifiedBlock = qcVoteData ∙ vdProposed

  -- getter only in Haskell
  qcParentBlock : Lens QuorumCert BlockInfo
  qcParentBlock = qcVoteData ∙ vdParent

  -- getter only in Haskell
  qcLedgerInfo : Lens QuorumCert LedgerInfoWithSignatures
  qcLedgerInfo = qcSignedLedgerInfo

  -- getter only in Haskell
  qcCommitInfo : Lens QuorumCert BlockInfo
  qcCommitInfo = qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo

  -- getter only in Haskell
  qcEndsEpoch : Lens QuorumCert Bool
  qcEndsEpoch = mkLens' g s
   where
    g : QuorumCert → Bool
    g q = is-just (q ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liNextEpochState)

    s : QuorumCert → Bool → QuorumCert
    s q _ = q -- TODO-1 : cannot be done: need a way to defined only getters

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

  -- not defined in Haskell
  qcCertifies : Lens QuorumCert  Hash
  qcCertifies = qcVoteData ∙ vdProposed ∙ biId

  -- not defined in Haskell
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

  postulate
    -- TODO-1 : Need to decide what empty means.
    --          Only important on epoch change.
    payloadIsEmpty : TX → Bool

  _≟BlockType_ : (b₁ b₂ : BlockType) → Dec (b₁ ≡ b₂)
  Genesis          ≟BlockType Genesis          = true because ofʸ refl
  NilBlock         ≟BlockType NilBlock         = true because ofʸ refl
  (Proposal t₁ a₁) ≟BlockType (Proposal t₂ a₂) with t₁ ≟ t₂
  ...| no  no-t = no λ where refl → no-t refl
  ...| yes refl with a₁ ≟ a₂
  ...| no  no-a = no λ where refl → no-a refl
  ...| yes refl = yes refl
  Genesis          ≟BlockType NilBlock       = no (λ ())
  Genesis          ≟BlockType (Proposal _ _) = no (λ ())
  NilBlock         ≟BlockType Genesis        = no (λ ())
  NilBlock         ≟BlockType (Proposal _ _) = no (λ ())
  (Proposal _ _)   ≟BlockType Genesis        = no (λ ())
  (Proposal _ _)   ≟BlockType NilBlock       = no (λ ())

  instance
    Eq-BlockType : Eq BlockType
    Eq._≟_ Eq-BlockType = _≟BlockType_

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

  -- not defined in Haskell
  bdParentId : Lens BlockData Hash
  bdParentId = bdQuorumCert ∙ qcVoteData ∙ vdParent ∙ biId

  -- not defined in Haskell
  -- This is the id of a block
  bdBlockId : Lens BlockData Hash
  bdBlockId = bdQuorumCert ∙ qcVoteData ∙ vdProposed ∙ biId

  -- getter only in Haskell
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

  -- getter only in Haskell
  bdPayload : Lens BlockData (Maybe TX)
  bdPayload = mkLens' g s
    where
    g : BlockData → Maybe TX
    g bd = case bd ^∙ bdBlockType of λ where
             (Proposal a _) → just a
             _              → nothing

    s : BlockData → Maybe TX → BlockData
    s bd _ = bd -- TODO-1 : cannot be done: need a way to define only getters


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

  -- getter only in Haskell
  bAuthor : Lens Block (Maybe Author)
  bAuthor = bBlockData ∙ bdAuthor

  -- getter only in Haskell
  bEpoch : Lens Block Epoch
  bEpoch = bBlockData ∙ bdEpoch

  -- getter only in Haskell
  bRound : Lens Block Round
  bRound = bBlockData ∙ bdRound

  -- getter only in Haskell
  bQuorumCert : Lens Block QuorumCert
  bQuorumCert  = bBlockData ∙ bdQuorumCert

  -- getter only in Haskell
  bParentId : Lens Block HashValue
  bParentId = bQuorumCert ∙ qcCertifiedBlock ∙ biId

  -- getter only in Haskell
  bPayload : Lens Block (Maybe TX)
  bPayload = bBlockData ∙ bdPayload

  infix 4 _≈Block_
  _≈Block_ : (b₁ b₂ : Block) → Set
  b₁ ≈Block b₂ = b₁ ≡ record b₂ { _bSignature = _bSignature b₁ }

  sym≈Block : Symmetric _≈Block_
  sym≈Block refl = refl

  record BlockRetriever : Set where
    constructor BlockRetriever∙new
    field
      _brDeadline      : Instant
      _brPreferredPeer : Author
  open BlockRetriever public
  unquoteDecl brDeadline   brPreferredPeer = mkLens (quote BlockRetriever)
             (brDeadline ∷ brPreferredPeer ∷ [])

  record AccumulatorExtensionProof : Set where
    constructor AccumulatorExtensionProof∙new
    field
      _aepObmNumLeaves : Version
  open AccumulatorExtensionProof public
  unquoteDecl aepObmNumLeaves = mkLens (quote AccumulatorExtensionProof)
             (aepObmNumLeaves ∷ [])

  record VoteProposal : Set where
    constructor VoteProposal∙new
    field
      _vpAccumulatorExtensionProof : AccumulatorExtensionProof
      _vpBlock : Block
      _vpNextEpochState : Maybe EpochState
  open VoteProposal public
  unquoteDecl  vpAccumulatorExtensionProof   vpBlock   vpNextEpochState = mkLens (quote VoteProposal)
              (vpAccumulatorExtensionProof ∷ vpBlock ∷ vpNextEpochState ∷ [])

  record MaybeSignedVoteProposal : Set where
    constructor MaybeSignedVoteProposal∙new
    field
      _msvpVoteProposal : VoteProposal
  open MaybeSignedVoteProposal public
  unquoteDecl  msvpVoteProposal = mkLens (quote MaybeSignedVoteProposal)
              (msvpVoteProposal ∷ [])

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
  TimeoutCertificate∙new to = mkTimeoutCertificate to Map.empty

  -- getter only in haskell
  tcEpoch : Lens TimeoutCertificate Epoch
  tcEpoch = tcTimeout ∙ toEpoch

  -- getter only in haskell
  tcRound : Lens TimeoutCertificate Round
  tcRound = tcTimeout ∙ toRound

  record SyncInfo : Set where
    constructor mkSyncInfo -- Bare constructor to enable pattern matching against SyncInfo; "smart"
                           -- constructor SyncInfo∙new is below
    field
      _siHighestQuorumCert  : QuorumCert
      _sixxxHighestCommitCert  : Maybe QuorumCert
      _siHighestTimeoutCert : Maybe TimeoutCertificate
  open SyncInfo public
  -- Note that we do not automatically derive a lens for siHighestCommitCert;
  -- it is defined manually below.
  unquoteDecl siHighestQuorumCert   sixxxHighestCommitCert   siHighestTimeoutCert = mkLens (quote SyncInfo)
             (siHighestQuorumCert ∷ sixxxHighestCommitCert ∷ siHighestTimeoutCert ∷ [])
  postulate instance enc-SyncInfo : Encoder SyncInfo

  SyncInfo∙new : QuorumCert → QuorumCert → Maybe TimeoutCertificate → SyncInfo
  SyncInfo∙new highestQuorumCert highestCommitCert highestTimeoutCert =
    record { _siHighestQuorumCert    = highestQuorumCert
           ; _sixxxHighestCommitCert = if highestQuorumCert QCBoolEq highestCommitCert
                                       then nothing else (just highestCommitCert)
           ; _siHighestTimeoutCert   = highestTimeoutCert }

  -- getter only in Haskell
  siHighestCommitCert : Lens SyncInfo QuorumCert
  siHighestCommitCert =
    mkLens' (λ x → fromMaybe (x ^∙ siHighestQuorumCert) (x ^∙ sixxxHighestCommitCert))
            (λ x qc → record x { _sixxxHighestCommitCert = just qc })

  -- getter only in Haskell
  siHighestCertifiedRound : Lens SyncInfo Round
  siHighestCertifiedRound = siHighestQuorumCert ∙ qcCertifiedBlock ∙ biRound

  -- getter only in Haskell
  siHighestTimeoutRound : Lens SyncInfo Round
  siHighestTimeoutRound =
    mkLens' (maybeHsk 0 (_^∙ tcRound) ∘ (_^∙ siHighestTimeoutCert))
            (λ x _r → x) -- TODO-1

  -- getter only in Haskell
  siHighestCommitRound : Lens SyncInfo Round
  siHighestCommitRound = siHighestCommitCert ∙ qcCommitInfo ∙ biRound

  -- getter only in Haskell
  siHighestRound : Lens SyncInfo Round
  siHighestRound =
    mkLens' (λ x → (x ^∙ siHighestCertifiedRound) ⊔ (x ^∙ siHighestTimeoutRound))
            (λ x _r → x) -- TODO-1

  -- getter only in Haskell
  siEpoch : Lens SyncInfo Epoch
  siEpoch  = siHighestQuorumCert ∙ qcCertifiedBlock ∙ biEpoch

  -- getter only in Haskell
  siObmRound : Lens SyncInfo Round
  siObmRound = siHighestQuorumCert ∙ qcCertifiedBlock ∙ biRound

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

  -- getter only in Haskell
  pmEpoch : Lens ProposalMsg Epoch
  pmEpoch = pmProposal ∙ bEpoch

  -- getter only in Haskell
  pmRound : Lens ProposalMsg Round
  pmRound = pmProposal ∙ bRound

  -- getter only in Haskell
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

  -- not defined in Haskell
  vmProposed : Lens VoteMsg BlockInfo
  vmProposed = vmVote ∙ vVoteData ∙ vdProposed

  -- not defined in Haskell
  vmParent : Lens VoteMsg BlockInfo
  vmParent = vmVote ∙ vVoteData ∙ vdParent

  -- getter-only in Haskell
  vmEpoch : Lens VoteMsg Epoch
  vmEpoch = vmVote ∙ vEpoch

  -- getter-only in Haskell
  vmRound : Lens VoteMsg Round
  vmRound = vmVote ∙ vRound

  -- IMPL-DIFF : This is defined without record fields in Haskell.
  -- The record fields below are never used.  But RootInfo must be a record for pattern matching.
  record RootInfo : Set where
    constructor RootInfo∙new
    field
      _riBlock : Block
      _riQC1   : QuorumCert
      _riQC2   : QuorumCert

  data RootMetadata : Set where RootMetadata∙new : RootMetadata

  record RecoveryData : Set where
    constructor mkRecoveryData
    field
      _rdLastVote                  : Maybe Vote
      _rdRoot                      : RootInfo
      _rdRootMetadata              : RootMetadata
      _rdBlocks                    : List Block
      _rdQuorumCerts               : List QuorumCert
      _rdBlocksToPrune             : Maybe (List HashValue)
      _rdHighestTimeoutCertificate : Maybe TimeoutCertificate
  open RecoveryData public
  unquoteDecl rdLastVote      rdRoot            rdRootMetadata                rdBlocks
              rdQuorumCerts   rdBlocksToPrune   rdHighestTimeoutCertificate = mkLens (quote RecoveryData)
             (rdLastVote    ∷ rdRoot          ∷ rdRootMetadata              ∷ rdBlocks ∷
              rdQuorumCerts ∷ rdBlocksToPrune ∷ rdHighestTimeoutCertificate ∷ [])

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

  record PendingVotes : Set where
    constructor mkPendingVotes
    field
      _pvLiDigestToVotes   : KVMap HashValue LedgerInfoWithSignatures
      _pvMaybePartialTC    : Maybe TimeoutCertificate
      _pvAuthorToVote      : KVMap Author Vote
  open PendingVotes public
  unquoteDecl pvLiDigestToVotes   pvMaybePartialTC   pvAuthorToVote = mkLens (quote PendingVotes)
             (pvLiDigestToVotes ∷ pvMaybePartialTC ∷ pvAuthorToVote ∷ [])

  PendingVotes∙new : PendingVotes
  PendingVotes∙new = mkPendingVotes Map.empty nothing Map.empty

  record StateComputeResult : Set where
    constructor StateComputeResult∙new
    field
      _scrObmNumLeaves : Version
      _scrEpochState   : Maybe EpochState
  open StateComputeResult public
  unquoteDecl scrObmNumLeaves   scrEpochState = mkLens (quote StateComputeResult)
             (scrObmNumLeaves ∷ scrEpochState ∷ [])

  postulate -- TODO: eliminate after fully implementing executeBlockE
    stateComputeResult : StateComputeResult

  record ExecutedBlock : Set where
    constructor ExecutedBlock∙new
    field
      _ebBlock              : Block
      _ebStateComputeResult : StateComputeResult
  open ExecutedBlock public
  unquoteDecl ebBlock   ebStateComputeResult = mkLens (quote ExecutedBlock)
             (ebBlock ∷ ebStateComputeResult ∷ [])

  -- getter only in Haskell
  ebId : Lens ExecutedBlock HashValue
  ebId = ebBlock ∙ bId

  -- getter only in Haskell
  ebQuorumCert : Lens ExecutedBlock QuorumCert
  ebQuorumCert = ebBlock ∙ bQuorumCert

  -- getter only in Haskell
  ebParentId : Lens ExecutedBlock HashValue
  ebParentId = ebQuorumCert ∙ qcCertifiedBlock ∙ biId

  -- getter only in Haskell
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

  -- getter only in Haskell
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

  record Waypoint : Set where
    constructor Waypoint∙new
    field
      _wVersion : Version
      _wValue   : HashValue
  open Waypoint public
  unquoteDecl wVersion   wValue = mkLens (quote Waypoint)
             (wVersion ∷ wValue ∷ [])
  postulate instance enc-Waypoint : Encoder Waypoint

  record PersistentSafetyStorage : Set where
    constructor mkPersistentSafetyStorage
    field
      _pssSafetyData : SafetyData
      _pssAuthor     : Author
      _pssWaypoint   : Waypoint
      _pssObmSK      : Maybe SK
  open PersistentSafetyStorage public
  unquoteDecl pssSafetyData   pssAuthor   pssWaypoint   pssObmSK = mkLens (quote PersistentSafetyStorage)
             (pssSafetyData ∷ pssAuthor ∷ pssWaypoint ∷ pssObmSK ∷ [])

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

  data ObmNotValidProposerReason : Set where
    ProposalDoesNotHaveAnAuthor ProposerForBlockIsNotValidForThisRound NotValidProposer : ObmNotValidProposerReason

  record ProposalGenerator : Set where
    constructor ProposalGenerator∙new
    field
      _pgLastRoundGenerated : Round
  open ProposalGenerator
  unquoteDecl pgLastRoundGenerated = mkLens (quote ProposalGenerator)
              (pgLastRoundGenerated ∷ [])

  record ProposerElection : Set where
    constructor ProposerElection∙new
    -- field
      -- _peProposers : Set Author
      -- _peObmLeaderOfRound : LeaderOfRoundFn
      -- _peObmNodesInOrder  : NodesInOrder
  open ProposerElection

  record SafetyRules : Set where
    constructor mkSafetyRules
    field
      _srPersistentStorage  : PersistentSafetyStorage
      _srExportConsensusKey : Bool
      _srValidatorSigner    : Maybe ValidatorSigner
      _srEpochState         : Maybe EpochState
  open SafetyRules public
  unquoteDecl srPersistentStorage   srExportConsensusKey   srValidatorSigner   srEpochState = mkLens (quote SafetyRules)
             (srPersistentStorage ∷ srExportConsensusKey ∷ srValidatorSigner ∷ srEpochState ∷ [])

  record BlockRetrievalRequest : Set where
    constructor BlockRetrievalRequest∙new
    field
      _brqObmFrom   : Author
      _brqBlockId   : HashValue
      _brqNumBlocks : U64
  open BlockRetrievalRequest public
  unquoteDecl brqObmFrom   brqBlockId   brqNumBlocks = mkLens (quote BlockRetrievalRequest)
             (brqObmFrom ∷ brqBlockId ∷ brqNumBlocks ∷ [])
  postulate instance enc-BlockRetrievalRequest : Encoder BlockRetrievalRequest

  data BlockRetrievalStatus : Set where
    BRSSucceeded BRSIdNotFound BRSNotEnoughBlocks : BlockRetrievalStatus
  open BlockRetrievalStatus public
  postulate instance enc-BlockRetrievalState : Encoder BlockRetrievalStatus

  brs-eq : (brs₁ brs₂ : BlockRetrievalStatus) → Dec (brs₁ ≡ brs₂)
  brs-eq BRSSucceeded       BRSSucceeded       = yes refl
  brs-eq BRSSucceeded       BRSIdNotFound      = no λ ()
  brs-eq BRSSucceeded       BRSNotEnoughBlocks = no λ ()
  brs-eq BRSIdNotFound      BRSSucceeded       = no λ ()
  brs-eq BRSIdNotFound      BRSIdNotFound      = yes refl
  brs-eq BRSIdNotFound      BRSNotEnoughBlocks = no λ ()
  brs-eq BRSNotEnoughBlocks BRSSucceeded       = no λ ()
  brs-eq BRSNotEnoughBlocks BRSIdNotFound      = no λ ()
  brs-eq BRSNotEnoughBlocks BRSNotEnoughBlocks = yes refl

  instance
    Eq-BlockRetrievalStatus : Eq BlockRetrievalStatus
    Eq._≟_ Eq-BlockRetrievalStatus = brs-eq

  record BlockRetrievalResponse : Set where
    constructor BlockRetrievalResponse∙new
    field
      _brpObmFrom : (Author × Epoch × Round) -- for logging
      _brpStatus  : BlockRetrievalStatus
      _brpBlocks  : List Block
  unquoteDecl brpObmFrom   brpStatus   brpBlocks   = mkLens (quote BlockRetrievalResponse)
             (brpObmFrom ∷ brpStatus ∷ brpBlocks ∷ [])
  postulate instance enc-BlockRetrievalResponse : Encoder BlockRetrievalResponse

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

  -- A block tree depends on a epoch config but works regardlesss of which
  -- EpochConfig we have.
  record BlockTree : Set where
    constructor mkBlockTree
    field
      _btIdToBlock               : KVMap HashValue LinkableBlock
      _btRootId                  : HashValue
      _btHighestCertifiedBlockId : HashValue
      _btHighestQuorumCert       : QuorumCert
      _btHighestTimeoutCert      : Maybe TimeoutCertificate
      _btHighestCommitCert       : QuorumCert
      _btIdToQuorumCert          : KVMap HashValue QuorumCert
      _btPrunedBlockIds          : VecDeque
      _btMaxPrunedBlocksInMem    : ℕ
  open BlockTree public
  unquoteDecl btIdToBlock   btRootId  btHighestCertifiedBlockId   btHighestQuorumCert
              btHighestTimeoutCert   btHighestCommitCert
              btIdToQuorumCert   btPrunedBlockIds
              btMaxPrunedBlocksInMem = mkLens (quote BlockTree)
             (btIdToBlock ∷ btRootId ∷ btHighestCertifiedBlockId ∷ btHighestQuorumCert ∷
              btHighestTimeoutCert ∷ btHighestCommitCert ∷
              btIdToQuorumCert ∷ btPrunedBlockIds ∷
              btMaxPrunedBlocksInMem ∷ [])

  btGetLinkableBlock : HashValue → BlockTree → Maybe LinkableBlock
  btGetLinkableBlock hv bt = Map.lookup hv (bt ^∙ btIdToBlock)

  btGetBlock : HashValue → BlockTree → Maybe ExecutedBlock
  btGetBlock hv bt = (_^∙ lbExecutedBlock) <$> btGetLinkableBlock hv bt

  -- getter only in Haskell
  btRoot : Lens BlockTree (Maybe ExecutedBlock)
  btRoot = mkLens' g s
    where
    g : BlockTree → Maybe ExecutedBlock
    g bt = btGetBlock (bt ^∙ btRootId) bt

    -- TODO-1 : the setter is not needed/defined in Haskell
    -- Defining it just to make progress, but it can't be defined
    -- correctly in terms of type correctness (let alone setting a new root!)
    s : BlockTree → Maybe ExecutedBlock → BlockTree
    s bt _ = bt -- TODO-1 : cannot be done: need a way to defined only getters

  -- getter only in haskell
  btHighestCertifiedBlock : Lens BlockTree (Maybe ExecutedBlock)
  btHighestCertifiedBlock = mkLens' g s
    where
    g : BlockTree → (Maybe ExecutedBlock)
    g bt = btGetBlock (bt ^∙ btHighestCertifiedBlockId) bt

    s : BlockTree → (Maybe ExecutedBlock) → BlockTree
    s bt _ = bt -- TODO-1 : cannot be done: need a way to defined only getters

  record LedgerStore : Set where
    constructor mkLedgerStore
    field
      _lsObmVersionToEpoch : Map.KVMap Version Epoch
      _lsObmEpochToLIWS    : Map.KVMap Epoch   LedgerInfoWithSignatures
      _lsLatestLedgerInfo  : Maybe LedgerInfoWithSignatures

  record DiemDB : Set where
    constructor DiemDB∙new
    field
      _ddbLedgerStore : LedgerStore
  open DiemDB public
  unquoteDecl ddbLedgerStore = mkLens (quote DiemDB)
             (ddbLedgerStore ∷ [])

  data ConsensusScheme : Set where ConsensusScheme∙new : ConsensusScheme
  -- instance S.Serialize ConsensusScheme

  record ValidatorSet : Set where
    constructor ValidatorSet∙new
    field
      _vsScheme  : ConsensusScheme
      _vsPayload : List ValidatorInfo
  -- instance S.Serialize ValidatorSet

  record MockSharedStorage : Set where
    constructor mkMockSharedStorage
    field
      -- Safety state
      _mssBlock                     : Map.KVMap HashValue Block
      _mssQc                        : Map.KVMap HashValue QuorumCert
      _mssLis                       : Map.KVMap Version   LedgerInfoWithSignatures
      _mssLastVote                  : Maybe Vote
      -- Liveness state
      _mssHighestTimeoutCertificate : Maybe TimeoutCertificate
      _mssValidatorSet              : ValidatorSet
  open MockSharedStorage public
  unquoteDecl mssBlock    mssQc   mssLis    mssLastVote
              mssHighestTimeoutCertificate  mssValidatorSet = mkLens (quote MockSharedStorage)
             (mssBlock ∷  mssQc ∷ mssLis ∷ mssLastVote ∷
              mssHighestTimeoutCertificate ∷ mssValidatorSet ∷ [])

  record MockStorage : Set where
    constructor MockStorage∙new
    field
      _msSharedStorage : MockSharedStorage
      _msStorageLedger : LedgerInfo
      _msObmDiemDB     : DiemDB
  open MockStorage public
  unquoteDecl msSharedStorage   msStorageLedger   msObmDiemDB = mkLens (quote MockStorage)
             (msSharedStorage ∷ msStorageLedger ∷ msObmDiemDB ∷ [])

  PersistentLivenessStorage = MockStorage

  record OnChainConfigPayload : Set where
    constructor OnChainConfigPayload∙new
    field
      _occpEpoch           : Epoch
      _occpObmValidatorSet : ValidatorSet
  open OnChainConfigPayload public
  unquoteDecl occpEpoch   occpObmValidatorSet = mkLens (quote OnChainConfigPayload)
             (occpEpoch ∷ occpObmValidatorSet ∷ [])
  -- instance S.Serialize OnChainConfigPayload

  record ReconfigEventEpochChange : Set where
    constructor ReconfigEventEpochChange∙new
    field
      _reecOnChainConfigPayload : OnChainConfigPayload
  -- instance S.Serialize ReconfigEventEpochChange

  -- IMPL-DIFF : Haskell StateComputer has pluggable functions.
  -- The Agda version just calls them directly
  record StateComputer : Set where
    constructor StateComputer∙new
    field
      _scObmVersion : Version
  open StateComputer public
  unquoteDecl scObmVersion = mkLens (quote StateComputer)
             (scObmVersion ∷ [])

  StateComputerComputeType
    = StateComputer → Block → HashValue
    → Either (List String) StateComputeResult

  StateComputerCommitType
    = StateComputer → DiemDB → ExecutedBlock → LedgerInfoWithSignatures
    → Either (List String) (StateComputer × DiemDB × Maybe ReconfigEventEpochChange)

  StateComputerSyncToType
    = LedgerInfoWithSignatures
    → Either (List String) ReconfigEventEpochChange

  record BlockStore : Set where
    constructor BlockStore∙new
    field
      _bsInner         : BlockTree
      _bsStateComputer : StateComputer
      _bsStorage       : PersistentLivenessStorage
  open BlockStore public
  unquoteDecl bsInner   bsStateComputer   bsStorage = mkLens (quote BlockStore)
             (bsInner ∷ bsStateComputer ∷ bsStorage ∷ [])

  postulate  -- TODO: stateComputer
    stateComputer : StateComputer

  -- getter only in Haskell
  bsRoot : Lens BlockStore (Maybe ExecutedBlock)
  bsRoot = bsInner ∙ btRoot

  -- getter only in Haskell
  bsHighestQuorumCert : Lens BlockStore QuorumCert
  bsHighestQuorumCert = bsInner ∙ btHighestQuorumCert

  -- getter only in Haskell
  bsHighestCommitCert : Lens BlockStore QuorumCert
  bsHighestCommitCert = bsInner ∙ btHighestCommitCert

  -- getter only in Haskell
  bsHighestTimeoutCert : Lens BlockStore (Maybe TimeoutCertificate)
  bsHighestTimeoutCert = bsInner ∙ btHighestTimeoutCert

  record LedgerRecoveryData : Set where
    constructor LedgerRecoveryData∙new
    field
      _lrdStorageLedger : LedgerInfo
