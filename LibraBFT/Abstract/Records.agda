open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types

module LibraBFT.Abstract.Records (ec : EpochConfig) (UID : Set) where

  record Block  : Set where
    constructor mkBlock
    field
      bId      : UID
      bAuthor  : Author ec
      bPrev    : Maybe UID -- nothing indicates it extends the initial
      bRound   : Round
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
   field
     qId            : UID
     qAuthor        : Author ec
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
  record IsLibraBFTRecord (A : Set) : Set where
    constructor is-librabft-record
    field
      getAuthor : A → Author ec -- TODO: REMOVE!
      getRound  : A → Round
  open IsLibraBFTRecord {{...}} public

  instance
    block-is-record : IsLibraBFTRecord Block
    block-is-record = is-librabft-record bAuthor bRound 

    vote-is-record : IsLibraBFTRecord Vote
    vote-is-record = is-librabft-record vAuthor vRound 

    qc-is-record : IsLibraBFTRecord QC
    qc-is-record = is-librabft-record qAuthor qRound 

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
  a ∈QC qc = Any (λ v → getAuthor v ≡ a) (qcVotes qc)

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

  uid : Record → Maybe UID
  uid I     = nothing
  uid (B b) = just (bId b)
  uid (Q q) = just (qId q)

  -- Each record has a round
  round : Record → Round
  round I     = 0
  round (B b) = getRound b
  round (Q q) = getRound q

