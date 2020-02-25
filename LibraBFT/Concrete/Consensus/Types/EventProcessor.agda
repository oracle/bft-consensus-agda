open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep
open import LibraBFT.Concrete.Util.KVMap
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import Optics.All

-- The event processor ties the knot and passes its own epoch config
-- to the blockstore.
module LibraBFT.Concrete.Consensus.Types.EventProcessor where

  abstractEpochConfig : SafetyRules → ValidatorVerifier → Maybe (Meta EpochConfig)
  abstractEpochConfig sr vv with (List-map proj₁ (kvm-toList (:vvAddressToValidatorInfo vv)))
  ...| validators with length validators | inspect length validators
  ...| numAuthors | [ numAuthors≡ ] with :vvQuorumVotingPower vv
  ...| qsize with numAuthors ∸ qsize
  ...| bizF with numAuthors ≥? suc (3 * bizF)
  ...| no  _  = nothing
  ...| yes xx = just (meta (mkEpochConfig
                                   (:psEpoch (:srPersistentStorage sr))
                                   (numAuthors)
                                   bizF
                                   xx
                                   0             -- TODO: what is this for?
                                   dummyHash     -- TODO: placeholder
                                   dummyHash     -- TODO: placeholder
                                   isVVAuthor))
       where isVVAuthor : NodeId → Maybe (Fin numAuthors)
             isVVAuthor nid with List-index {AccountAddress} _≟AccountAddress_ nid validators
             ...| nothing    = nothing
             ...| just found = just (cast numAuthors≡ found)

  record EventProcessor : Set where
    constructor mkEventProcessor
    field
      :epEpochConfig  : Meta EpochConfig
      :epBlockStore   : BlockStore {:epEpochConfig}
      :epSafetyRules  : SafetyRules
      :epValidators   : ValidatorVerifier
      :epECCorrect    : Meta (just :epEpochConfig ≡ abstractEpochConfig :epSafetyRules :epValidators)
  open EventProcessor public

  -- NOTE: In Haskell, we have the following definitions:
  --
  -- instance RWBlockStore (EventProcessor a) a where
  --   lBlockStore = lens _epBlockStore (\x y -> x { _epBlockStore = y})
  --
  -- instance RWBlockTree (EventProcessor a) a where
  --   lBlockTree = lens (^.epBlockStore.bsInner) (\x y -> x & epBlockStore.bsInner .~ y)
  --
  -- However, We cannot have useful lenses for EventProcessor, because changing any of the real fields
  -- potentially requires proofs to be updated or proved unchanged, for which lenses do not receieve
  -- enough information.

  -- Therefore, we will need to work around this.
