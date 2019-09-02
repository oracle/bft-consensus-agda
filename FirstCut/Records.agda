open import Prelude
open import BasicTypes

module Records {f : ℕ} (ec : EpochConfig f)  where

  record Block (a : Author ec) : Set where
    constructor mkBlock
    field
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
      --bSignature  : Signature
  open Block public 

  record Vote (a : Author ec) : Set where
    field
      --vEpoch     : EpochId
      vRound     : Round
      vBlockHash : BlockHash
      --vState     : State
      --vSignature : Signature
  open Vote public

 -- QuorumCertificate ------------------------------
  qSize : ℕ
  qSize = authorsN ec ∸ f

  -- TODO: check if this exists
  enum : (n : ℕ) → List (Fin n)
  enum 0       = []
  enum (suc n) = zero ∷ map suc (enum n)

  -- This is the type that has at least min votes for different authors coming from at most max authors
  data QCVec : (min : ℕ) → List (Author ec) → Set where
    -- If we ever want to record the supeflouous votes, we can always resort to
    -- smthing like:
    --  > enough : ∀ {a}     → All (Maybe ∘ Vote) a → QCVec 0 a
    -- For now, lets see if we can get by ignoring those
    enough : ∀ {as}     → QCVec 0 as
    skip   : ∀ {m a as} → QCVec m as
                        → QCVec m (a ∷ as)
    voted  : ∀ {m a as} → Vote a
                        → QCVec m as
                        → QCVec (suc m) (a ∷ as)

  record QC (a : Author ec) : Set where
    field
      --qEpoch         : EpochId
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : QCVec qSize (enum (authorsN ec))
  open QC public

  record Initial : Set where
    constructor mkInitial
    field
      iSeed    : ℕ
  open Initial public

  record Timeout (a : Author ec) : Set where
    constructor mkTimeout
    field
      toRound   : Round
      --toSignature : Signature
  open Timeout public

  data Record : Set where
    I : Initial → Record
    B : ∀ {a} → Block a   → Record
    Q : ∀ {a} → QC a      → Record
    V : ∀ {a} → Vote a    → Record
    T : ∀ {a} → Timeout a → Record



