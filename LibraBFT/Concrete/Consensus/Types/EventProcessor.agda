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

  record EventProcessor {ec : Meta EpochConfig} : Set where
    constructor mkEventProcessor
    field
      :epBlockStore   : BlockStore {ec}
      :epSafetyRules  : SafetyRules
      :epValidators   : ValidatorVerifier
  open EventProcessor public

  abstractEpochConfig : SafetyRules → ValidatorVerifier → Maybe (Meta EpochConfig)
  abstractEpochConfig sr vv with (List-map proj₁ (kvm-toList (:vvAddressToValidatorInfo vv)))
  ...| validators with length validators | inspect length validators
  ...| numAuthors | [ numAuthors≡ ] with :vvQuorumVotingPower vv
  ...| qsize with numAuthors ∸ qsize
  ...| bizF with numAuthors ≥? suc (3 * bizF)
  ...| no  _  = nothing
  ...| yes xx with allDistinct? {≟A = _≟_} validators
  ...| no  _  = nothing
  ...| yes distinct = just (meta (mkEpochConfig
                                   (:psEpoch (:srPersistentStorage sr))
                                   (numAuthors)
                                   bizF
                                   xx
                                   0  -- TODO: what is this for?
                                   dummyHash
                                   dummyHash
                                   isVVAuthor))
       where isVVAuthor : NodeId → Maybe (Fin numAuthors)
             isVVAuthor nid with List-index {AccountAddress} _≟AccountAddress_ nid validators
             ...| nothing    = nothing
             ...| just found = just (cast numAuthors≡ found)

  record EventProcessorWrapper : Set where
    constructor mkEventProcessorWrapper
    field
      :epwEpochConfig    : Meta EpochConfig
      :epwEventProcessor : EventProcessor {:epwEpochConfig}
      _epwECCorrect      : Meta (just :epwEpochConfig ≡
                                 abstractEpochConfig (:epSafetyRules :epwEventProcessor)
                                                     (:epValidators :epwEventProcessor))
  open EventProcessorWrapper public

{-
 
  unquoteDecl epEpochConfig   epBlockStore epValidators = mkLens (quote EventProcessor)
             (epEpochConfig ∷ epBlockStore ∷ epValidators ∷ [])

  -- Actually, makes sense lens don't work for dependent types
  -- that easily: the type we really want here is:
  --
  -- Lens (e : EventProcessor) (BlockStore (_epEpochConfig e))
  -- 
  -- Now, recall that Lens S A = (A -> F A) -> S -> F S, forall F;
  -- Then, the above would have to be isomorphic to:
  --
  -- (BlockStore (_epEpochConfig e) → F (BlockStore (_epEpochConfig e))
  --   → (e : EventProcessor) → F EventProcessor
  -- 
  -- which makes no sense! 'e' is not in scope before its needed. Perhaps,
  -- then, we could conceive the type:
  --
  -- (∀ {ec} → BlockStore ec → F (BlockStore ec)) → EventProcessor → F EventProcessor
  --
  -- But now we lost the informatino about the projection being over
  -- the "right" ec.
  -- 


-}

  lBlockStore : ∀ {ec : Meta EpochConfig} → Lens (EventProcessor {ec}) (BlockStore {ec})
  lBlockStore {ec} = mkLens' :epBlockStore λ ep bs → record ep { :epBlockStore = bs}

  lBlockTree : ∀ {ec : Meta EpochConfig} → Lens (EventProcessor {ec}) (BlockTree {ec})
  lBlockTree {ec} = lBlockStore ∙ bsInner
