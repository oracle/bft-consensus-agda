open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types using (isAuthor)
open import LibraBFT.Concrete.Types
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import LibraBFT.Concrete.Util.KVMap

-- This is our clone of Libra/Consensus/Types.hs
module LibraBFT.Concrete.Records (pki : PKI) where

  -- TODO:
  -- VCM: Think about this; wy not make /Meta/ into something like
  -- the IO monad? No comming out of it!
  postulate
    Meta : Set → Set
    onMeta : {A B : Set} → (A → B) → Meta A → Meta B

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
  postulate instance enc-LedgerInfo : Encoder LedgerInfo


  record LedgerInfoWithSignatures : Set where
    constructor mkLedgerInfoWithSignatures
    field
      liwsLedgerInfo : LedgerInfo
      liwsSignatures : KVMap Author Signature
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

      -- The algo should never /read/ metadata. 
      vOrderMeta        : Meta ℕ
  open Vote public
  postulate instance enc-Vote : Encoder Vote

  record QuorumCert : Set where
    constructor mkQuorumCert
    field
      qcVoteData         : VoteData
      qcSignedLedgerInfo : LedgerInfoWithSignatures
  open QuorumCert public
  postulate instance enc-QuorumCert : Encoder QuorumCert

  qcVotesKV : QuorumCert → KVMap Author Signature
  qcVotesKV qc = liwsSignatures (qcSignedLedgerInfo qc)

  qcVotes : QuorumCert → List (Author × Signature)
  qcVotes qc = kvm-toList (qcVotesKV qc)

  qcCertifies : QuorumCert → Hash
  qcCertifies qc = biId (vdParent (qcVoteData qc))

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

  ----------------------
  -- Network Messages --
  ----------------------

  record SyncInfo : Set where
    constructor mkSyncInfo
    field
      siHighestQuorumCert  : QuorumCert
      siHighestCommitCert  : QuorumCert
      -- siHighestTimeoutCert : Mabe TimeoutCert -- VCM: TODO: define 
  postulate instance enc-SyncInfo : Encoder SyncInfo

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

  data NetworkMsg (A : Set) : Set where
    P : ProposalMsg A → NetworkMsg A
    V : VoteMsg       → NetworkMsg A
    C : CommitMsg     → NetworkMsg A

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  instance 
   -- A Block might carry a signature
   sig-Block : {A : Set} ⦃ encA : Encoder A ⦄ → WithSig (Block A)
   sig-Block = record
      { Signed         = Is-just ∘ bSignature 
      ; isSigned?      = λ b → Maybe-Any-dec (λ _ → yes tt) (bSignature b)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ b → concat (encodeH (bId b) ∷ encode (bBlockData b) ∷ []) 
      }
  
   -- A proposal message might carry a signature inside the block it
   -- is proposing.
   sig-ProposalMsg : {A : Set} ⦃ encA : Encoder A ⦄ → WithSig (ProposalMsg A)
   sig-ProposalMsg = record
      { Signed         = Signed         ∘ pmProposal 
      ; isSigned?      = isSigned?      ∘ pmProposal
      ; signature      = signature      ∘ pmProposal 
      ; signableFields = signableFields ∘ pmProposal 
      }

   -- A vote is always signed; as seen by the 'Unit'
   -- on the definition of Signed.
   -- VCM-QUESTION: What are the signable fields? What do we
   -- do with timeoutSignature?
   sig-Vote : WithSig Vote
   sig-Vote = record 
      { Signed         = λ _ → Unit 
      ; isSigned?      = λ _ → yes unit
      ; signature      = λ v _ → vSignature v 
      ; signableFields = λ v → concat {!!} 
      }

   sig-VoteMsg : WithSig VoteMsg
   sig-VoteMsg = record
      { Signed         = Signed         ∘ vmVote
      ; isSigned?      = isSigned?      ∘ vmVote
      ; signature      = signature      ∘ vmVote
      ; signableFields = signableFields ∘ vmVote
      }

   sig-commit : WithSig CommitMsg
   sig-commit = record
      { Signed         = Is-just ∘ cSigMB 
      ; isSigned?      = λ c → Maybe-Any-dec (λ _ → yes tt) (cSigMB c)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ c → concat ( encode  (cEpochId c) 
                                      ∷ encode  (cAuthor c) 
                                      ∷ encode  (cRound c) 
                                      ∷ encodeH (cCert c) 
                                      ∷ []) 
      }

  ---------------------------------------------------------
  -- Network Records whose signatures have been verified --
  ---------------------------------------------------------

  data VerNetworkMsg (A : Set) ⦃ encA : Encoder A ⦄ : Set where
    P : (p : ProposalMsg A) → WithVerSig p → VerNetworkMsg A
    V : (v : VoteMsg)       → WithVerSig v → VerNetworkMsg A
    C : (c : CommitMsg)     → WithVerSig c → VerNetworkMsg A


