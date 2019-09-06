open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.BasicTypes

module LibraBFT.Abstract.EpochConfig where

  -- An 'EpochConfig f' carries the information we need tot
  -- survive at most 'f' byzantine failures. for now, this is
  -- only a lower bound on the number of overal authors.
  record EpochConfig (f : ℕ) : Set where
    field
      epochId  : EpochId
      authorsN : ℕ
      isBFT    : authorsN ≥ suc (3 * f)

      -- seed  : ℕ
    QuorumSize : ℕ
    QuorumSize = authorsN ∸ f
  open EpochConfig public

  -- An author, on the other hand, is a participant that
  -- is supposed to be active in a given epoch. 
  -- It is therefore identifed in an epoch by a finite type.
  Author : ∀ {f} → EpochConfig f → Set
  Author ec = Fin (authorsN ec)

