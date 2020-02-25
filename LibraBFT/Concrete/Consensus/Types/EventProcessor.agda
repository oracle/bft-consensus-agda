{-# OPTIONS --allow-unsolved-metas #-}

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

  -- These are the parts of the event processor that
  -- depend on a epoch config. We do not particularly care
  -- which epoch config they care about yet.
  record EventProcessorWithEC (ec : Meta EpochConfig) : Set where
    constructor mkEventProcessor
    field
      :epBlockStore   : BlockStore ec
  open EventProcessorWithEC public
    -- VCM: Oh... lenses are still not working in this case. No idea why.
    -- I would need to spend too much time; not sure its worthwhile
    -- unquoteDecl epBlockStore = mkLens (quote EventProcessorWithEC)
    --  (epBlockStore ∷ [])

  -- Some of the EventProcessor pieces contain the
  -- necessary information to build an EpochConfig out of.
  record EventProcessorEC : Set where
    constructor mkEventProcessorPreEC
    field
      :epSafetyRules  : SafetyRules
      :epValidators   : ValidatorVerifier
  open EventProcessorEC public

  -- Naturally, we need this info to be correct.
  -- We enforce this with a predicate that these pieces are alright, things
  -- such as numAuthors ≥? suc (3 * bizF) etc
  EventProcessorEC-correct : EventProcessorEC → Set
  EventProcessorEC-correct _ = Unit -- TODO

  -- This will be a copy of abstractEC which I moved below; 
  -- but since we are carrying a proof of correctness, we do not
  -- need to return a Maybe
  α-EC : Σ EventProcessorEC EventProcessorEC-correct → Meta EpochConfig
  α-EC _ = {!!}

  -- Finally, the EventProcessor is split in two pieces: those
  -- that are used to make an epoch config versus those that 
  -- use an epoch config.
  
  record EventProcessor : Set where
    constructor mkEventProcessor
    field
      :epEC           : EventProcessorEC 
      :epEC-correct   : EventProcessorEC-correct :epEC
      :epWithEC       : EventProcessorWithEC (α-EC (:epEC , :epEC-correct))
     -- VCM: I think that if we want to add pieces that neither contribute
     -- to the construction of the EC nor need one, they should come
     -- in EventProcessor directly
  open EventProcessor public

  -- VCM: OLD CODE BELOW!

{-
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
-}


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
