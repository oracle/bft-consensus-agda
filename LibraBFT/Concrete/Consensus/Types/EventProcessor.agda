open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep

open import Optics.All

-- The event processor ties the knot and passes its own epoch config
-- to the blockstore.
module LibraBFT.Concrete.Consensus.Types.EventProcessor where

  record EventProcessor (ec : EpochConfig) : Set where
    constructor eventProcessor
    field
      _epBlockStore   : BlockStore ec
      _epValidators   : List Author  -- TODO: ValidatorVerifier details
  open EventProcessor public

  -- This looks a bit weird because we need to parameterize EventProcessor by _some_ EpochConfig
  -- before we can compute the right EpochConfig from it.  Not sure if there's a better way, but I
  -- think this would work OK because the mythical function will of course not refer to the
  -- EpochConfig passed to the module, as it will only reference "real" parts of the EventProcessor.
  -- A side benefit is that we won't have to reason that the EpochConfig doesn't change whenever we
  -- modify something else in the EventProcessor that doesn't actually change epochs.
  postulate
    mythicalAbstractionFunction : ∀ {ec : EpochConfig} → EventProcessor ec → EpochConfig

  record EventProcessorWrapper : Set where
    field
      _epwEpochConfig    : EpochConfig
      _epwEventProcessor : EventProcessor _epwEpochConfig
      _epwECCorrect      : _epwEpochConfig ≡ mythicalAbstractionFunction _epwEventProcessor
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

  lBlockStore : ∀ (ec : EpochConfig) → Lens (EventProcessor ec) (BlockStore ec)
  lBlockStore ec = mkLens' _epBlockStore λ ep bs → record ep { _epBlockStore = bs}

  lBlockTree : ∀ (ec : EpochConfig) → Lens (EventProcessor ec) (BlockTree ec)
  lBlockTree ec = (lBlockStore ec) ∙ (bsInner ec)
