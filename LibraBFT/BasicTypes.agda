open import LibraBFT.Prelude
open import LibraBFT.Hash

-- Exposition of the ground types that we build our abstract reasoning
-- over. 
module LibraBFT.BasicTypes where

  -- An 'EpochConfig f' carries the information we need tot
  -- survive at most 'f' byzantine failures. for now, this is
  -- only a lower bound on the number of overal authors.
  record EpochConfig (f : ℕ) : Set where
    field
      epochId  : ℕ
      authorsN : ℕ
      isBFT    : authorsN ≥ suc (3 * f)

      -- seed  : ℕ
    QuorumSize : ℕ
    QuorumSize = authorsN ∸ f
  open EpochConfig public

  -- An author is identifed in an epoch by a finite type.
  Author : ∀ {f} → EpochConfig f → Set
  Author ec = Fin (authorsN ec)

  Round : Set
  Round = ℕ

  Command : Set
  Command = ℕ

  QCHash : Set
  QCHash = Hash

  BlockHash : Set
  BlockHash = Hash

  Signature : Set
  Signature = Hash

  State : Set
  State = Hash

