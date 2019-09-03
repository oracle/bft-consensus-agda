open import Prelude
open import BasicTypes

-- Here we provide abstract definitions of
-- verified records, that is, we assume that
-- they have been received through the wire and
-- validated accordingly. This include:
--
--  1) Well-formedness of different fields
--  2) Sender have been aute'ed against an epoch.
--  3) Signatures have been verified
-- 
module Records {f : ℕ} (ec : EpochConfig f)  where

  -- TODO: discuss if we want to keep signatures here.
  --  VCM: I'm leaning towards leaving signatures out and
  --       handlign these on the validation layer.

  record Block  : Set where
    constructor mkBlock
    field
      bAuthor     : Author ec
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
      --bSignature  : Signature
  open Block public 

  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  record Vote  : Set where
    constructor mkVote
    field
      vAuthor    : Author ec
      vRound     : Round
      vBlockHash : BlockHash
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

  -- Extends an arbitrary relation to work on the head of
  -- the supplied list, if any.
  data OnHead {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []  : OnHead P x []
    _∷_ : ∀{y ys} → P x y → OnHead P x (y ∷ ys)

  -- Estabilishes that a list is sorted according to the supplied
  -- relation.
  data IsSorted {A : Set}(_<_ : A → A → Set) : List A → Set where
    []  : IsSorted _<_ []
    _∷_ : ∀{x xs} → OnHead _<_ x xs → IsSorted _<_ xs → IsSorted _<_ (x ∷ xs)

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
    V : Vote      → Record
    T : Timeout   → Record

  -- Each record has a round
  round : Record → Round
  round (I i) = 0 -- (FOR MARK) here we said that the round of the
                  -- initial record is zero. Do you think this is ok or
                  -- should we return a 'Maybe Round'? Using zero makes life simpler though.
  round (B b) = bRound b
  round (Q q) = qRound q
  round (V v) = vRound v
  round (T t) = toRound t
