open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- This module brings in the base types used through libra
-- and those necessary for the abstract model.
module LibraBFT.Abstract.Types where
  
  open import LibraBFT.Base.Types public

  -- VCM: After our discussion about vote order; I propose
  -- we make it into a postulate. Naturally, as the name suggests,
  -- it must have some sort of order raltion; also inacessible.

  -- MSM: But then how can we create values of this type in the concrete model?
  --      I am making it ℕ for now.  Of course, this makes it accessible to those
  --      that shouldn't access it, but I think that should be addressed by convention,
  --      e.g. naming fields of this type with an AUX suffix, enabling searching and
  --      careful examination of each use to ensure it's not accessed where it shouldn't be.

  {- 
  postulate
    VoteOrder : Set
    _<VO_     : VoteOrder → VoteOrder → Set
   -}
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
