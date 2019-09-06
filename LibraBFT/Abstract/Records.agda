{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

-- Here we provide abstract definitions of
-- verified records, that is, we assume that
-- they have been received through the wire and
-- validated accordingly. This include:
--
--  1) Well-formedness of different fields
--  2) Sender have been aute'ed against an epoch.
--  3) Signatures have been verified
-- 
module LibraBFT.Abstract.Records {f : ℕ} (ec : EpochConfig f)  
  -- A Hash function maps a bytestring into a hash.
  (hash     : ByteString → Hash)
  -- And is colission resistant
  (hash-cr  : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  record Block  : Set where
    constructor mkBlock
    field
      bAuthor     : Author ec
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
  open Block public 

  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  record Vote  : Set where
    constructor mkVote
    field
      vAuthor    : Author ec
      vBlockHash : BlockHash
      vRound     : Round
      -- The 'vOrder' is a "metafield", it keeps track of which vote from 'vAuthor'
      -- this is representing. This makes it much simpler to talk about thinks such as 
      -- the increasing round rule. 
      vOrder     : ℕ 
      --vState     : State
      --vSignature : Signature
  open Vote public

  -- * Quorum Certificates
  --
  -- These are intersting. A Valid quorum certificate contains
  -- at least 'QuorumSize ec' votes from different authors.
  -- 
  -- We achive that by considering a sorted list of 'Vote's
  -- with the _<_ relation from Data.Fin, which also guarantees
  -- the authors are different. 

  record QC : Set₁ where
    field
      qAuthor        : Author ec
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : List Vote
      -- Here are the coherence conditions. Firstly, we expect
      -- 'qVotes' to be sorted, which guarnatees distinct authors.
      qVotes-C1      : IsSorted (λ v₀ v₁ → vAuthor v₀ <Fin vAuthor v₁) qVotes 
      -- Secondly, we expect it to have at least 'QuorumSize' number of
      -- votes, for the particular epoch in question.
      qVotes-C2      : QuorumSize ec ≤ length qVotes
      -- All the votes must vote for the qBlockHash in here;
      qVotes-C3      : All (λ v → vBlockHash v ≡ qBlockHash) qVotes
      -- Likewise for rounds
      qVotes-C4      : All (λ v → vRound v ≡ qRound) qVotes
  open QC public

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
  a ∈QC qc = Any (λ v → vAuthor v ≡ a) (qVotes qc)

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{a : Author ec} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q


  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- The initial record is unique per epoch. Essentially, we just
  -- use the 'epochSeed' and the hash of the last record of the previous
  -- epoch to piggyback the initial record.
  data Initial : Set where
    mkInitial : Initial

  -- TODO: We are not handling timeouts yet
  record Timeout : Set where
    constructor mkTimeout
    field
      toAuthor  : Author ec
      toRound   : Round
      --toSignature : Signature
  open Timeout public

  -- A record is defined by being either of the types introduced above.
  data Record : Set₁ where
    I : Initial   → Record
    B : Block     → Record
    Q : QC        → Record
    -- V : Vote      → Record
    -- T : Timeout   → Record

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  -- Each record has a round
  round : Record → Round
  round (I i) = 0
  round (B b) = bRound b
  round (Q q) = qRound q
  -- round (V v) = vRound v
  -- round (T t) = toRound t

  -- We need to encode records into bytestrings in order to hash them.
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR : Record → Hash
  HashR = hash ∘ encodeR

  data _←_ : Record → Record → Set where
    I←B : {i : Initial} {b : Block}
          → HashR (I i) ≡  bPrevQCHash b
          → I i ← B b
    Q←B : {q : QC} {b : Block}
          → HashR (Q q) ≡  bPrevQCHash b
          → Q q ← B b
    B←Q : {b : Block} {q : QC}
          → HashR (B b) ≡ qBlockHash q
          → B b ← Q q
    -- B←V : {b : Block} {v : Vote}
    --       → HashR (B b) ≡ vBlockHash v
    --       → B b ← V v

