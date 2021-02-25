{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig
open WithAbsVote

-- This module defines abstract records (the initial or "genesis" record, blocks, and quorum
-- certificates), along with related definitions and properties.

module LibraBFT.Abstract.Records
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁)) -- Needed to prove ≟Block and ≈?QC
    (NodeId : Set)
    (𝓔 : EpochConfig UID NodeId)
    (𝓥 : VoteEvidence UID NodeId 𝓔)
 where

  open import LibraBFT.Abstract.Types UID NodeId
  open EpochConfig 𝓔

  -- Abstract blocks do /not/ need to carry the state hash. Since the
  -- state hash of a concrete block is supposed to be hashed in the
  -- UID of an abstract one; the connection between states is implicit.
  -- Our proofs all work modulo injectivity of UID anyway.
  record Block  : Set where
    constructor mkBlock
    field
      bRound   : Round
      bId      : UID
      bPrevQC  : Maybe UID -- 'nothing' indicates it extends the genesis block.
  open Block public

  Block-η : {b b' : Block}
         → bRound b ≡ bRound b'
         → bId b ≡ bId b'
         → bPrevQC b ≡ bPrevQC b'
         → b ≡ b'
  Block-η refl refl refl = refl

  -- We define a Vote as an AbsVoteData applied
  -- to the correct parameters; This helps in defining
  -- and manipulating the 𝓥 vote evidence predicate.
  Vote : Set
  Vote = AbsVoteData UID NodeId 𝓔

  vRound      : Vote → Round
  vRound      = abs-vRound

  vMember     : Vote → EpochConfig.Member 𝓔
  vMember     = abs-vMember

  vBlockUID   : Vote → UID
  vBlockUID   = abs-vBlockUID

  Vote-η : {v v' : Vote}
         → vRound v ≡ vRound v' → vMember v ≡ vMember v'
         → vBlockUID v ≡ vBlockUID v'
         → v ≡ v'
  Vote-η refl refl refl = refl

  -- * Quorum Certificates
  --
  -- A valid quorum certificate contains at least 'QuorumSize ec'
  -- votes from different authors.
  record QC : Set where
   constructor mkQC
   field
     qRound         : Round
     qCertBlockId   : UID -- this is the id for the block it certifies.
     qVotes         : List Vote
     -- The voters form a quorum
     qVotes-C1      : IsQuorum (List-map vMember qVotes)
     -- All votes are for the same blockId
     qVotes-C2      : All (λ v → vBlockUID v ≡ qCertBlockId) qVotes
     -- Likewise for rounds
     qVotes-C3      : All (λ v → vRound v ≡ qRound) qVotes
     -- And we have evidence for all votes
     qVotes-C4      : All 𝓥 qVotes
  open QC public

  ------------------------
  -- QC's make a setoid --
  ------------------------

  -- Two QC's are said to be equivalent if they have the same ID;
  -- that is, they certify the same block. As we are talking about
  -- /abstract/ QCs, we have proofs that both have at least QuorumSize
  -- votes for /the same block/!
  --
  -- It might be tempting to want qRound q₀ ≡ qRound q₁ in here,
  -- but the proof of ←-≈Rec in LibraBFT.Abstract.Records.Extends
  -- would be impossible.
  _≈QC_ : QC → QC → Set
  q₀ ≈QC q₁ = qCertBlockId q₀ ≡ qCertBlockId q₁

  _≈QC?_ : (q₀ q₁ : QC) → Dec (q₀ ≈QC q₁)
  q₀ ≈QC? q₁ with qCertBlockId q₀ ≟UID qCertBlockId q₁
  ...| yes refl = yes refl
  ...| no  neq  = no λ x → neq x

  ≈QC-refl : Reflexive _≈QC_
  ≈QC-refl = refl

  ≈QC-sym : Symmetric _≈QC_
  ≈QC-sym refl = refl

  ≈QC-trans : Transitive _≈QC_
  ≈QC-trans refl x = x

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

  -- Accessing common fields in different Records types is a nuissance; yet, Blocks,
  -- votes and QC's all have three important common fields: author, round and maybe the
  -- ID of a previous record.  Therefore we declare a type-class that provide "getters"
  -- for commonly used fields.
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

  _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)
  b₀ ≟Block b₁
     with bRound b₀ ≟ bRound b₁
  ...| no neq = no λ x → neq (cong bRound x)
  ...| yes r≡
     with (bId b₀) ≟UID (bId b₁)
  ...| no neq = no λ x → neq (cong bId x)
  ...| yes i≡
     with Maybe-≡-dec {A = UID} _≟UID_ (bPrevQC b₀) (bPrevQC b₁)
  ...| no neq = no λ x → neq (cong bPrevQC x)
  ...| yes p≡ = yes (Block-η r≡ i≡ p≡)

  qcVotes : QC → List Vote
  qcVotes = qVotes

  -- Now we can state whether an author has voted in a given QC.
  _∈QC_  : Member → QC → Set
  a ∈QC qc = Any (λ v → vMember v ≡ a) (qcVotes qc)

  ∈QC-Member : ∀{α}(q : QC)(v : α ∈QC q)
             → α ≡ vMember (List-lookup (qcVotes q) (Any-index v))
  ∈QC-Member {α} q v = aux v
    where
      aux : ∀{vs}(p : Any (λ v → vMember v ≡ α) vs)
          → α ≡ vMember (List-lookup vs (Any-index p))
      aux (here px) = sym px
      aux (there p) = aux p

  -- Gets the vote of a ∈QC
  -- TODO-1: make q explicit; a implicit
  ∈QC-Vote : {a : Member} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q

  ∈QC-Vote-correct : ∀ q → {a : Member} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qcVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- Same vote in two QC's means the QCs are equivalent
  ∈QC-Vote-≈ : {v : Vote}{q q' : QC}
             → v ∈ qcVotes q → v ∈ qcVotes q'
             → q ≈QC q'
  ∈QC-Vote-≈ {v} {q} {q'} vq vq'
    = trans (sym (All-lookup (qVotes-C2 q)  vq))
                 (All-lookup (qVotes-C2 q') vq')

  -- A record is either one of the types introduced above or the initial/genesis record.
  data Record : Set where
    I :             Record
    B : Block     → Record
    Q : QC        → Record

  -- Records are equivalent if and only if they are either not
  -- QCs and propositionally equal or they are equivalent qcs.
  data _≈Rec_ : Record → Record → Set where
    eq-I :                        I    ≈Rec I
    eq-Q : ∀{q₀ q₁} → q₀ ≈QC q₁ → Q q₀ ≈Rec Q q₁
    eq-B : ∀{b₀ b₁} → b₀  ≡  b₁ → B b₀ ≈Rec B b₁

  ≈Rec-refl : Reflexive _≈Rec_
  ≈Rec-refl {I}   = eq-I
  ≈Rec-refl {B x} = eq-B refl
  ≈Rec-refl {Q x} = eq-Q (≈QC-refl {x})

  ≈Rec-sym : Symmetric _≈Rec_
  ≈Rec-sym {I}         eq-I       = eq-I
  ≈Rec-sym {B x}       (eq-B prf) = eq-B (sym prf)
  ≈Rec-sym {Q x} {Q y} (eq-Q prf) = eq-Q (≈QC-sym {x} {y} prf)

  ≈Rec-trans : Transitive _≈Rec_
  ≈Rec-trans {I}                eq-I      eq-I      = eq-I
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

  -- Record unique ids carry whether the abstract id was assigned
  -- to a QC or a Block; this can be useful to avoid having to deal
  -- with 'blockId ≟ initialAgreedID' in order to decide whether
  -- a block is the genesis block or not.
  data TypedUID : Set where
    id-I   : TypedUID
    id-B∨Q : UID -> TypedUID

  id-I≢id-B∨Q : ∀{id} → id-I ≡ id-B∨Q id → ⊥
  id-I≢id-B∨Q ()

  id-B∨Q-inj : ∀{u₁ u₂} → id-B∨Q u₁ ≡ id-B∨Q u₂ → u₁ ≡ u₂
  id-B∨Q-inj refl = refl

  uid : Record → TypedUID
  uid I     = id-I
  uid (B b) = id-B∨Q (bId   b)
  uid (Q q) = id-B∨Q (qCertBlockId q)

  -- Each record has a round
  round : Record → Round
  round I     = 0
  round (B b) = getRound b
  round (Q q) = getRound q
