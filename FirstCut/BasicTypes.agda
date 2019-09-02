open import Data.Nat
open import Data.Fin
open import Hash

module BasicTypes where

  record EpochConfig (f : ℕ) : Set where
    field
      epochId  : ℕ
      authorsN : ℕ
      isBFT    : authorsN ≥ suc (3 * f)
  open EpochConfig public

  Author : ∀ {f} → EpochConfig f → Set
  Author ec = Fin (authorsN ec)

  -- We must not inspect who is honest and who is not
  -- We will use a postulate and produce values of said type using module parameters
  postulate
    Honest : ∀ {f} {ec : EpochConfig f} → Author ec → Set
    -- Later in the future we can implement this as an abstract

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

