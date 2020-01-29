open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.Records (ec : EpochConfig) (UID : B∨QC → Set) where

  record Block  : Set where
    constructor mkBlock
    field
      bId      : UID tB
      bAuthor  : Author ec
      bPrev    : Maybe (UID tQC) -- 'nothing' indicates it extends the genesis block.
      bRound   : Round
      -- bResult : StateHash
  open Block public

  record Vote  : Set where
    constructor mkVote
    field
      vAuthor    : Author ec
      vBlockUID  : UID tB
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
     qId            : UID tQC -- this is the id for this QC
     qPrev          : UID tB  -- this is the id for the block it certifies.
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

  ------------------------
  -- QC's make a setoid --
  ------------------------
   
  _≈QC_ : QC → QC → Set
  q₀ ≈QC q₁ = qId q₀   ≡ qId q₁
            × qPrev q₀ ≡ qPrev q₁

  ≈QC-refl : Reflexive _≈QC_
  ≈QC-refl = (refl , refl)

  ≈QC-sym : Symmetric _≈QC_
  ≈QC-sym (refl , refl) = (refl , refl)

  ≈QC-trans : Transitive _≈QC_
  ≈QC-trans (refl , refl) x = x

  QC-setoid : Setoid ℓ0 ℓ0
  QC-setoid = record 
    { Carrier       = QC 
    ; _≈_           = _≈QC_ 
    ; isEquivalence = record 
        { refl  = λ {q}         → ≈QC-refl {q}
        ; sym   = λ {q} {u}     → ≈QC-sym {q} {u}
        ; trans = λ {q} {u} {l} → ≈QC-trans {q} {u} {l} 
        } 
    }
 
{-
  _≈QC_ : QC → QC → Set
  q₀ ≈QC q₁ = qId q₀    ≡ qId q₁
            × qPrev q₀  ≡ qPrev q₁
            × qRound q₀ ≡ qRound q₁

  ≈QC-refl : Reflexive _≈QC_
  ≈QC-refl = (refl , refl , refl)

  ≈QC-sym : Symmetric _≈QC_
  ≈QC-sym (refl , refl , refl) = (refl , refl , refl)

  ≈QC-trans : Transitive _≈QC_
  ≈QC-trans (refl , refl , refl) x = x

  QC-setoid : Setoid ℓ0 ℓ0
  QC-setoid = record 
    { Carrier       = QC 
    ; _≈_           = _≈QC_ 
    ; isEquivalence = record 
        { refl  = λ {q}         → ≈QC-refl {q}
        ; sym   = λ {q} {u}     → ≈QC-sym {q} {u}
        ; trans = λ {q} {u} {l} → ≈QC-trans {q} {u} {l} 
        } 
    }
-}
  

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
  -- postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

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

  data _≈Rec_ : Record → Record → Set where
    eq-I :                        I    ≈Rec I
    eq-Q : ∀{q₀ q₁} → q₀ ≈QC q₁ → Q q₀ ≈Rec Q q₁
    eq-B : ∀{b₀ b₁} → b₀  ≡  b₁ → B b₀ ≈Rec B b₁

  ≈Rec-refl : Reflexive _≈Rec_
  ≈Rec-refl {I} = eq-I
  ≈Rec-refl {B x} = eq-B refl
  ≈Rec-refl {Q x} = eq-Q (≈QC-refl {x})

  ≈Rec-sym : Symmetric _≈Rec_
  ≈Rec-sym {I}         eq-I       = eq-I
  ≈Rec-sym {B x}       (eq-B prf) = eq-B (sym prf)
  ≈Rec-sym {Q x} {Q y} (eq-Q prf) = eq-Q (≈QC-sym {x} {y} prf)

  ≈Rec-trans : Transitive _≈Rec_
  ≈Rec-trans {I}               eq-I      eq-I      = eq-I
  ≈Rec-trans {B x}             (eq-B p₀) (eq-B p₁) = eq-B (trans p₀ p₁)
  ≈Rec-trans {Q x} {Q y} {Q z} (eq-Q p₀) (eq-Q p₁) = eq-Q (≈QC-trans {x} {y} {z} p₀ p₁)

  Rec-setoid : Setoid ℓ0 ℓ0
  Rec-setoid = record 
    { Carrier       = Record
    ; _≈_           = _≈Rec_ 
    ; isEquivalence = record 
        { refl  = λ {q}         → ≈Rec-refl {q}
        ; sym   = λ {q} {u}     → ≈Rec-sym {q} {u}
        ; trans = λ {q} {u} {l} → ≈Rec-trans {q} {u} {l} 
        } 
    }
  
  postulate _≈Rec?_   : (r s : Record) → Dec (r ≈Rec s)
  -- postulate _≟Record_ : (r s : Record) → Dec (r ≡ s)

{-
  B≢Q : ∀{b q} → B b ≡ Q q → ⊥
  B≢Q ()

  Q-injective : ∀{q q'} → Q q ≡ Q q' → q ≡ q'
  Q-injective refl = refl

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl
-}

  -- Record unique ids carry whether the abstract id was assigned
  -- to a QC or a Block; in fact, we only care about injectivity
  -- modulo the same type. No two blocks with the same UID nor
  -- two QCs with the same UID; 
  data TypedUID : Set where
    id-I : TypedUID
    id-Q : UID tQC -> TypedUID
    id-B : UID tB  -> TypedUID

  uid : Record → TypedUID
  uid I     = id-I
  uid (B b) = id-B (bId b)
  uid (Q q) = id-Q (qId q)

  -- Each record has a round
  round : Record → Round
  round I     = 0
  round (B b) = getRound b
  round (Q q) = getRound q

