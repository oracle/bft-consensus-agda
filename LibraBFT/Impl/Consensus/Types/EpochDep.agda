{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types.EpochIndep
open import LibraBFT.Impl.Util.Crypto
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

module LibraBFT.Impl.Consensus.Types.EpochDep (𝓔 : EpochConfig) where
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
    constructor mkIsValidVote
    inductive
    field
      ₋ivvMember   : Member
      ₋ivvAuthor   : isMember? (₋vAuthor v) ≡ just ₋ivvMember
      ₋ivvSigned   : WithVerSig (getPubKey ₋ivvMember) v

      ₋ivvVDhash   : v ^∙ vLedgerInfo ∙ liConsensusDataHash ≡ hashVD (v ^∙ vVoteData)

      -- A valid vote must vote for a block that exists and is
      -- inserted in a RecordChain.
      ₋ivvBlock    : Abs.Block
      ₋ivvBlockId  : v ^∙ vProposedId ≡ Abs.bId ₋ivvBlock

      -- Moreover; we must check that the 'parent' field of the vote is coherent.
      ₋ivvCoherent : VoteCoherence v ₋ivvBlock

      -- Finally, the vote is for the correct epoch
      ₋ivvEpoch    : v ^∙ vEpoch ≡ epochId
      ₋ivvEpoch2   : v ^∙ vParent ∙ biEpoch ≡ epochId  -- Not needed?
  open IsValidVote public

  -- A valid vote can be directly mapped to an AbsVoteData. Abstraction of QCs
  -- and blocks will be given in LibraBFT.Concrete.Records, since those are
  -- more involved functions.
  α-ValidVote : (v : Vote) → Member → AbsVoteData
  α-ValidVote v mbr = mkAbsVoteData (v ^∙ vProposed ∙ biRound)
                                     mbr
                                     (v ^∙ vProposed ∙ biId)

  -- α-ValidVote is the same for two votes that have the same vAuthor, vdProposed and vOrder
  α-ValidVote-≡ : ∀ {cv v'} {m : Member}
                → ₋vdProposed (₋vVoteData cv) ≡ ₋vdProposed (₋vVoteData v')
                → α-ValidVote cv m ≡ α-ValidVote v' m
  α-ValidVote-≡ {cv} {v'} prop≡ =
    AbsVoteData-η (cong ₋biRound prop≡) refl (cong ₋biId prop≡)

  -- Finally; evidence for some abstract vote consists of a concrete valid vote
  -- that is coherent with the abstract vote data.
  record ConcreteVoteEvidence vd where
    constructor mkCVE
    inductive
    field
      ₋cveVote        : Vote
      ₋cveIsValidVote : IsValidVote ₋cveVote
      ₋cveIsAbs       : α-ValidVote ₋cveVote (₋ivvMember ₋cveIsValidVote) ≡ vd
  open ConcreteVoteEvidence public

  -- Gets the signature of a concrete vote evidence
  ₋cveSignature : ∀{vd} → ConcreteVoteEvidence vd → Signature
  ₋cveSignature = ₋vSignature ∘ ₋cveVote

  -- A valid quorum certificate contains a collection of valid votes, such that
  -- the members represented by those votes (which exist because the votes are valid)
  -- constitutes a quorum.
  record IsValidQC (qc : QuorumCert) : Set where
    field
      ₋ivqcVotesValid      : All (IsValidVote ∘ rebuildVote qc) (qcVotes qc)
      ₋ivqcIsQuorum        : IsQuorum (All-reduce ₋ivvMember ₋ivqcVotesValid)
  open IsValidQC public

  vqcMember : (qc : QuorumCert) → IsValidQC qc
             → ∀ {as} → as ∈ qcVotes qc → Member
  vqcMember qc v {α , _ , _} as∈qc with All-lookup (₋ivqcVotesValid v) as∈qc
  ...| prf = ₋ivvMember prf

  -- A block tree depends on a epoch config but works regardlesss of which
  -- EpochConfig we have.
  record BlockTree : Set where
    constructor mkBlockTree
    field
      ₋btIdToBlock               : KVMap HashValue LinkableBlock
      ₋btRootId                  : HashValue
      ₋btHighestCertifiedBlockId : HashValue
      ₋btHighestQuorumCert       : QuorumCert
      -- btHighestTimeoutCert      : Maybe TimeoutCertificate
      ₋btHighestCommitCert       : QuorumCert
      ₋btPendingVotes            : PendingVotes
      ₋btPrunedBlockIds          : List HashValue
      ₋btMaxPrunedBlocksInMem    : ℕ
      ₋btIdToQuorumCert          : KVMap HashValue (Σ QuorumCert IsValidQC)
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
      ₋bsInner         : BlockTree
      -- bsStateComputer : StateComputer
      -- bsStorage       : CBPersistentStorage
  open BlockStore public
  unquoteDecl bsInner = mkLens (quote BlockStore)
             (bsInner ∷ [])

  -- These are the parts of the EventProcessor that depend on an
  -- EpochConfig. We do not particularly care which EpochConfig
  -- they care about yet.
  --
  record EventProcessorWithEC : Set where
    constructor mkEventProcessorWithEC
    field
      ₋epBlockStore   : BlockStore
  open EventProcessorWithEC public
  unquoteDecl epBlockStore = mkLens (quote EventProcessorWithEC)
    (epBlockStore ∷ [])

  lBlockTree : Lens EventProcessorWithEC BlockTree
  lBlockTree = epBlockStore ∙ bsInner
