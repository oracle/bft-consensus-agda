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
    Meta : Set → Set
    Meta x = x

    unsafeReadMeta : {X : Set} → Meta X → X
    unsafeReadMeta x = x

    meta : {X : Set} → X → Meta X
    meta x = x

    Meta-map : {X Y : Set} → (X → Y) → Meta X → Meta Y
    Meta-map f x = f x

    Meta-bind : {X Y : Set} → Meta X → (X → Meta Y) → Meta Y
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
  record EpochConfig : Set where
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

  open EpochConfig public
