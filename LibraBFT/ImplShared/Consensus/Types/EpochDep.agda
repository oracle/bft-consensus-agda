{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

-- This module defines the types that depend on an EpochConfig,
-- but never inspect it. Consequently, we define everyting over
-- an abstract 𝓔 passed around as a module parameter.
--
-- Importantly, though, we are connecting abstract and concrete
-- votes by defining what constitutes enough "evidence" that a
-- vote was cast, which is passed around in the abstract model as
-- the variable (𝓥 : VoteEvidence); here we instantiate it to
-- 'ConcreteVoteEvidence'.
--
-- TODO-3: update types to reflect more recent version of LibraBFT.
-- This is a substantial undertaking that should probably be led by
-- someone who can access our internal implementation.
--
-- TODO-4: Make the Optics.Reflection stuff work with record
-- parameters, so we can merge all modules back into Types.  For
-- now, this is the easiest way to avoid the issue that making a
-- module inside Consensus.Types called EpochDep will break
-- mkLens (not sure why).

module LibraBFT.ImplShared.Consensus.Types.EpochDep (𝓔 : EpochConfig) where
  open EpochConfig 𝓔
  open WithAbsVote 𝓔

  -- A 'ConcreteVoteEvidence' is a piece of information that
  -- captures that the 'vd : AbsVoteData' in question was not /invented/
  -- but instead, comes from a concrete vote that is /valid/ (that is,
  -- signature has been checked and author belongs to this epoch).
  --
  -- Moreover, we will also store the RecordChain that leads to the vote;
  -- this requires some mutually-recursive shenanigans, so we first declare
  -- ConcreteVoteEvidence, then import the necessary modules, and then define it.
  record ConcreteVoteEvidence (vd : AbsVoteData) : Set

  open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 ConcreteVoteEvidence as Abs hiding (qcVotes; Vote)

  data VoteCoherence (v : Vote) (b : Abs.Block) : Set where
    initial  : v ^∙ vParentId    ≡ genesisUID
             → v ^∙ vParentRound ≡ 0
             → Abs.bPrevQC b     ≡ nothing
             → VoteCoherence v b

    ¬initial : ∀{b' q}
             → v ^∙ vParentId    ≢ genesisUID
             → v ^∙ vParentRound ≢ 0
             → v ^∙ vParentId    ≡ Abs.bId b'
             → v ^∙ vParentRound ≡ Abs.bRound b'
             → (Abs.B b') ← (Abs.Q q)
             → (Abs.Q q)  ← (Abs.B b)
             → VoteCoherence v b

  -- Estabilishing validity of a concrete vote involves checking:
  --
  --   i) Vote author belongs to the current epoch
  --  ii) Vote signature is correctly verified
  -- iii) Existence of a RecordChain up to the voted-for block.
  --  iv) Coherence of 'vdParent' field with the above record chain.
  --
  record IsValidVote (v : Vote) : Set where
    constructor IsValidVote∙new
    inductive
    field
      _ivvMember   : Member
      _ivvAuthor   : isMember? (_vAuthor v) ≡ just _ivvMember
      _ivvSigned   : WithVerSig (getPubKey _ivvMember) v

      _ivvVDhash   : v ^∙ vLedgerInfo ∙ liConsensusDataHash ≡ hashVD (v ^∙ vVoteData)

      -- A valid vote must vote for a block that exists and is
      -- inserted in a RecordChain.
      _ivvBlock    : Abs.Block
      _ivvBlockId  : v ^∙ vProposedId ≡ Abs.bId _ivvBlock

      -- Moreover; we must check that the 'parent' field of the vote is coherent.
      _ivvCoherent : VoteCoherence v _ivvBlock

      -- Finally, the vote is for the correct epoch
      _ivvEpoch    : v ^∙ vEpoch ≡ epoch
      _ivvEpoch2   : v ^∙ vParent ∙ biEpoch ≡ epoch  -- Not needed?
  open IsValidVote public

  -- A valid vote can be directly mapped to an AbsVoteData. Abstraction of QCs
  -- and blocks will be given in LibraBFT.Concrete.Records, since those are
  -- more involved functions.
  α-ValidVote : (v : Vote) → Member → AbsVoteData
  α-ValidVote v mbr = AbsVoteData∙new (v ^∙ vProposed ∙ biRound)
                                      mbr
                                      (v ^∙ vProposed ∙ biId)

  -- α-ValidVote is the same for two votes that have the same vAuthor, vdProposed and vOrder
  α-ValidVote-≡ : ∀ {cv v'} {m : Member}
                → _vdProposed (_vVoteData cv) ≡ _vdProposed (_vVoteData v')
                → α-ValidVote cv m ≡ α-ValidVote v' m
  α-ValidVote-≡ {cv} {v'} prop≡ =
    AbsVoteData-η (cong _biRound prop≡) refl (cong _biId prop≡)

  -- Finally; evidence for some abstract vote consists of a concrete valid vote
  -- that is coherent with the abstract vote data.
  record ConcreteVoteEvidence vd where
    constructor CVE∙new
    inductive
    field
      _cveVote        : Vote
      _cveIsValidVote : IsValidVote _cveVote
      _cveIsAbs       : α-ValidVote _cveVote (_ivvMember _cveIsValidVote) ≡ vd
  open ConcreteVoteEvidence public

  -- Gets the signature of a concrete vote evidence
  _cveSignature : ∀{vd} → ConcreteVoteEvidence vd → Signature
  _cveSignature = _vSignature ∘ _cveVote

  -- A valid quorum certificate contains a collection of valid votes, such that
  -- the members represented by those votes (which exist because the votes are valid)
  -- constitutes a quorum.
  record MetaIsValidQC (qc : QuorumCert) : Set where
    field
      _ivqcMetaVotesValid      : All (IsValidVote ∘ rebuildVote qc) (qcVotes qc)
      _ivqcMetaIsQuorum        : IsQuorum (All-reduce _ivvMember _ivqcMetaVotesValid)
  open MetaIsValidQC public

  vqcMember : (qc : QuorumCert) → MetaIsValidQC qc
             → ∀ {as} → as ∈ qcVotes qc → Member
  vqcMember qc v {α , _ , _} as∈qc with All-lookup (_ivqcMetaVotesValid v) as∈qc
  ...| prf = _ivvMember prf

  -- A block tree depends on a epoch config but works regardlesss of which
  -- EpochConfig we have.
  record BlockTree : Set where
    constructor BlockTree∙new
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
      _btIdToQuorumCert          : KVMap HashValue (Σ QuorumCert MetaIsValidQC)
  open BlockTree public
  unquoteDecl btIdToBlock   btRootId   btHighestCertifiedBlockId   btHighestQuorumCert
              btHighestCommitCert   btPendingVotes   btPrunedBlockIds
              btMaxPrunedBlocksInMem btIdToQuorumCert = mkLens (quote BlockTree)
             (btIdToBlock ∷ btRootId ∷ btHighestCertifiedBlockId ∷ btHighestQuorumCert ∷
              btHighestCommitCert ∷ btPendingVotes ∷ btPrunedBlockIds ∷
              btMaxPrunedBlocksInMem ∷ btIdToQuorumCert ∷ [])

  record BlockStore : Set where
    constructor BlockStore∙new
    field
      _bsInner         : BlockTree
      -- bsStateComputer : StateComputer
      -- bsStorage       : CBPersistentStorage
  open BlockStore public
  unquoteDecl bsInner = mkLens (quote BlockStore)
             (bsInner ∷ [])

  -- These are the parts of the RoundManager that depend on an
  -- EpochConfig. We do not particularly care which EpochConfig
  -- they care about yet.
  --
  record RoundManagerWithEC : Set where
    constructor RoundManagerWithEC∙new
    field
      _epBlockStore   : BlockStore
  open RoundManagerWithEC public
  unquoteDecl epBlockStore = mkLens (quote RoundManagerWithEC)
    (epBlockStore ∷ [])

  lBlockTree : Lens RoundManagerWithEC BlockTree
  lBlockTree = epBlockStore ∙ bsInner
