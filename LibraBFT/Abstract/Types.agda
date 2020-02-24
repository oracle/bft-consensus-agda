open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- This module brings in the base types used through libra
-- and those necessary for the abstract model.
module LibraBFT.Abstract.Types where
  
  open import LibraBFT.Base.Types public

  -- The abstract model might need access to meta information that
  -- comes from the concrete model; To ensure we do not /read/
  -- metainformation without thinking about it, we will put it in
  -- a monad just like Haskell's IO; we call it Meta.
  --
  -- Abstract blocks are used to define constructs that we do /not/
  -- want to reduce outside their block. Their purpose is
  -- to speed typechecking or separate concerns. Outside of the
  -- abstract block, all definitions are treated as postulates;
  -- think of them as typechecked postulates.
  abstract
    Meta : ∀{ℓ} → Set ℓ → Set ℓ
    Meta x = x

    unsafeReadMeta : ∀{x}{X : Set x} → Meta X → X
    unsafeReadMeta x = x

    meta : ∀{x}{X : Set x} → X → Meta X
    meta x = x

    Meta-map : ∀{x y}{X : Set x}{Y : Set y} → (X → Y) → Meta X → Meta Y
    Meta-map f x = f x

    Meta-bind : ∀{x y}{X : Set x}{Y : Set y} → Meta X → (X → Meta Y) → Meta Y
    Meta-bind x f = f x

  -- VoteOrder is a natural number, but the concrete model
  -- treats it as a 'Meta' concept. We don't want to put it
  -- inside the Meta-monad on the abstract model since we constantly 
  -- use it in abstract-land; if we encapsulated if in Meta we'd
  -- have to use 'unsafeReadMeta' everywhere. 
  VoteOrder : Set
  VoteOrder = ℕ

  _<VO_     : VoteOrder → VoteOrder → Set
  _<VO_ = _<_

  -- An 'EpochConfig' carries the information we need to
  -- survive at most 'bizF' byzantine failures.
  -- TODO: Generalize for different voting power, same as Rust and (future) Haskell code
  record EpochConfig : Set where
    constructor mkEpochConfig
    field
      epochId  : EpochId
      authorsN : ℕ
      bizF     : ℕ

      isBFT    : authorsN ≥ suc (3 * bizF)

      seed     : ℕ

      ecInitialState  : State
  
      initialAgreedHash : Hash

    QuorumSize : ℕ
    QuorumSize = authorsN ∸ bizF

    Author     : Set
    Author     = Fin authorsN

    field
      isAuthor   : NodeId → Maybe Author   -- TODO: Arguably NodeId should be abstracted out here

    -- We must not inspect who is honest and who is not
    -- We will use a postulate and produce values of said type using
    -- other postulates that must be carefully checked by hand.
    --
    -- However, the way I have expressed here that the number of Byzantine participants is correct
    -- depends on a Dec (Honest α), which must not be accessed by the algorithm.  Therefore we instead
    -- use Meta (Dec (Honest α)) so that it cannot be accidentally used in the algorithm.
    -- 
    -- Note, bizF is an upper bound on the number of dishonest ones, but we can just require the
    -- number to be equal to bizF: if there are fewer than bizF dishonest ones, the additional
    -- "dishonest" ones can emulate honest ones, so we don't need to model the exact number of
    -- dishonest ones.

    postulate
      Honest : Author → Set
      ?Honest : (α : Author) → Dec (Meta (Honest α))
      EnoughHonest : length (List-filter ?Honest (fins authorsN)) ≡ bizF

  open EpochConfig public
