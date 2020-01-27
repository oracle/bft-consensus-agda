open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types

module LibraBFT.Abstract.Records (ec : EpochConfig) (UID : Set) where

  record Block  : Set where
    constructor mkBlock
    field
      bId      : UID
      bAuthor  : Author ec
      bPrev    : Maybe UID -- 'nothing' indicates it extends the genesis block.
      bRound   : Round
      -- bResult : StateHash
  open Block public

  record Vote  : Set where
    constructor mkVote
    field
      vAuthor    : Author ec
      vBlockUID  : UID
      vRound     : Round
      vOrder     : VoteOrder 
      --vState     : State
  open Vote public

  -- * Quorum Certificates
  --
  -- These are intersting. A Valid quorum certificate contains
  -- at least 'QuorumSize ec' votes from different authors.
  -- 
  -- We achive that by considering a sorted list of 'Vote's
  -- with the _<_ relation from Data.Fin, which also guarantees
  -- the authors are different. 
  record QC : Set where
   constructor mkQC
   field
     -- Can a block have many QCs? yes; but that seems to hardly
     -- influence anything. We could identify a qc directly 
     -- by the id of the block it certifies.
     --
     -- MSM: I am not convinced.  It is quite possible that we will have two different QCs in our
     -- BlockTree that certify the same block (e.g., we add one, then fail to reach consensus on it,
     -- we time out and another leader produces another proposal including a different QC that
     -- certifies the same block.  The concrete model cannot eliminate the possibility of a
     -- NonInjective for these different QCs and therefore gets nothing from the abstract
     -- properties.  AFAICT, the only issue is that we might get a NonInjective from
     -- RecordChain-irrelevant (all other NonInjectives stem from injectivity failures on blocks,
     -- not QCs, I think).  Therefore, we need to either eliminate the need for
     -- RecordChain-irrelevant in our abstract proof, or make sure that the UIDs for the (abstract)
     -- QCs associated with concrete QCs that certify the same block are different.
     --
     --
     -- MSM: I don't follow this part.  This is how the blockstore is, and therefore
     -- what we should model.  The question is how we come up with IDs based on this,
     -- not the other way around.
     --
     -- The blockstore then becomes just like the implementation:
     --  >  pub struct BlockTree<T> {
     --  >     /// All the blocks known to this replica (with parent links)
     --  >     id_to_block: HashMap<HashValue, LinkableBlock<T>>,
     --  >     ...
     --  >     /// Map of block id to its completed quorum certificate (2f + 1 votes)
     --  >     id_to_quorum_cert: HashMap<HashValue, Arc<QuorumCert>>,
     --  >     ...
     --  >  }
     --
     -- qId            : UID
     qPrev          : UID -- previous block identifier
     qRound         : Round
     qVotes         : List Vote
     --qState         : State
     -- Here are the coherence conditions. Firstly, we expect
     -- 'qVotes' to be sorted, which guarnatees distinct authors.
     qVotes-C1      : IsSorted (λ v₀ v₁ → vAuthor v₀ <Fin vAuthor v₁) qVotes
     -- Secondly, we expect it to have at least 'QuorumSize' number of
     -- votes, for the particular epoch in question.
     qVotes-C2      : QuorumSize ec ≤ length qVotes
     -- All the votes must vote for the qBlockHash in here;
     qVotes-C3      : All (λ v → vBlockUID v ≡ qPrev) qVotes
     -- Likewise for rounds
     qVotes-C4      : All (λ v → vRound v ≡ qRound) qVotes
  open QC public

  -- Accessing the fields start to be a nuissance; yet, Blocks,
  -- votes and QC's all have three important common fields: author, round and prevHash.
  -- I'll make the same trick as Harold and declare a type-class that gives
  -- the getters for the stuff we need all the time.
  record HasRound (A : Set) : Set where
    constructor is-librabft-record
    field
      getRound  : A → Round
  open HasRound {{...}} public

  instance
    block-is-record : HasRound Block
    block-is-record = is-librabft-record bRound 

    vote-is-record : HasRound Vote
    vote-is-record = is-librabft-record vRound 

    qc-is-record : HasRound QC
    qc-is-record = is-librabft-record qRound 

  -- TODO: Implement
  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  voteOrder : Vote → VoteOrder
  voteOrder = vOrder 
    
  qcVotes : QC → List Vote
  qcVotes = qVotes 

  -- TODO:
  -- VCM: Lisandra notes that we might not need propositional equality on quorum certificates.
  -- I agree. We can define our own equivalence relation comparing the size of the list, the author,
  -- the round and the blockhash. We don't particuarly care about the votes!
  -- 
  -- For now, anyway, I'll just postulate decidable equality of what we currently have.
  postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

  -- It's pretty easy to state whether an author has voted in
  -- a given QC.
  _∈QC_  : Author ec → QC → Set
  a ∈QC qc = Any (λ v → vAuthor v ≡ a) (qcVotes qc)

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{a : Author ec} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q


  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qcVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- A record is defined by being either of the types introduced above.
  --
  -- VCM: TODO: Shouldn't we take the new BlockStore
  -- approach and couple blocks and QCs on the same datatype?
  -- Yes, its a major effort, but I believe it will pay off
  -- in helping to distinguish network records from records supposed
  -- to be stored in the block store.
  data Record : Set where
    I :             Record
    B : Block     → Record
    Q : QC        → Record

  postulate _≟Record_ : (r s : Record) → Dec (r ≡ s)

  B≢Q : ∀{b q} → B b ≡ Q q → ⊥
  B≢Q ()

  Q-injective : ∀{q q'} → Q q ≡ Q q' → q ≡ q'
  Q-injective refl = refl

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  -- Record unique ids carry whether the abstract id was assigned
  -- to a QC or a Block; in fact, we only care about injectivity
  -- modulo the same type. No two blocks with the same UID nor
  -- two QCs with the same UID; 
  data TypedUID : Set where
    id-I : TypedUID
    id-Q : UID -> TypedUID
    id-B : UID -> TypedUID

  uid : Record → TypedUID
  uid I     = id-I
  uid (B b) = id-B (bId   b)
  uid (Q q) = id-Q (qPrev q)

  -- Each record has a round
  round : Record → Round
  round I     = 0
  round (B b) = getRound b
  round (Q q) = getRound q

