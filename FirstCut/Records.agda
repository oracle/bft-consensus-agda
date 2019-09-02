open import Prelude
open import BasicTypes

module Records {f : ℕ} (ec : EpochConfig f)  where

  record Block  : Set where
    constructor mkBlock
    field
      bAuthor     : Author ec
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
      --bSignature  : Signature
  open Block public 

  record Vote  : Set where
    field
      vAuthor    : Author ec
      --vEpoch     : EpochId
      vRound     : Round
      vBlockHash : BlockHash
      --vState     : State
      --vSignature : Signature
  open Vote public

 -- QuorumCertificate ------------------------------
  qSize : ℕ
  qSize = authorsN ec ∸ f

    
  data TC {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []  : TC P x []
    _∷_ : ∀{y ys} → P x y → TC P x (y ∷ ys)

  data IsSorted {A : Set}(_<_ : A → A → Set) : List A → Set where
    []  : IsSorted _<_ []
    _∷_ : ∀{x xs} → TC _<_ x xs → IsSorted _<_ xs → IsSorted _<_ (x ∷ xs)

  record QC : Set₁ where
    field
      qAuthor        : Author ec
      --qEpoch         : EpochId
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : List Vote
      qVotes-C1      : IsSorted (λ v₀ v₁ → vAuthor v₀ <Fin vAuthor v₁) qVotes 
      qVotes-C2      : qSize ≤ length qVotes
  open QC public

  -- VCM: Lisandra notes that we might not need propositional equality on quorum certificates.
  -- I agree. We can define our own equivalence relation comparing the size of the list, the author,
  -- the round and the blockhash. We don't particuarly care about the votes!
  -- 
  -- For now, anyway, I'll just postulate decidable equality of what we currently have.
  postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

  _∈QC_  : Author ec → QC → Set
  a ∈QC qc = Any (λ v → vAuthor v ≡ a) (qVotes qc)

  -- The initial record is unique per epoch. Essentially, we just
  -- use the 'epochSeed' and the hash of the last record of the previous
  -- epoch to piggyback the initial record.
  data Initial : Set where
    mkInitial : Initial

  record Timeout : Set where
    constructor mkTimeout
    field
      toAuthor  : Author ec
      toRound   : Round
      --toSignature : Signature
  open Timeout public

  data Record : Set₁ where
    I : Initial   → Record
    B : Block     → Record
    Q : QC        → Record
    V : Vote      → Record
    T : Timeout   → Record

  round : Record → Round
  round (I i) = 0
  round (B b) = bRound b
  round (Q q) = qRound q
  round (V v) = vRound v
  round (T t) = toRound t

