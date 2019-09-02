open import Prelude
open import Hash

-- Exposition of the ground types that we build our abstract reasoning
-- over. 
module BasicTypes where

  -- An 'EpochConfig f' carries the information we need tot
  -- survive at most 'f' byzantine failures. for now, this is
  -- only a lower bound on the number of overal authors.
  record EpochConfig (f : ℕ) : Set where
    field
      epochId  : ℕ
      authorsN : ℕ
      isBFT    : authorsN ≥ suc (3 * f)

    QuorumSize : ℕ
    QuorumSize = authorsN ∸ f
  open EpochConfig public

  -- An author is identifed in an epoch by a finite type.
  Author : ∀ {f} → EpochConfig f → Set
  Author ec = Fin (authorsN ec)

  -- TODO: Prove the BFT assumption. Feels like its just arithmetic,
  -- but these are famous last words after the skiplog stuff, huh? :)

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

