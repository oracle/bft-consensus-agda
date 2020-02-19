open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.Types.EpochDep

open import Optics.All

-- The event processor ties the knot and passes its own epoch config
-- to the blockstore.
module LibraBFT.Concrete.Consensus.Types.EventProcessor where

  record EventProcessor : Set where
    constructor eventProcessor
    field
      _epEpochConfig  : EpochConfig  -- TODO: this should be a function of the "real" parts of EventProcessor
      _epBlockStore   : BlockStore _epEpochConfig
      _epValidators   : List Author  -- TODO: ValidatorVerifier details
  open EventProcessor public
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
  lBlockStore : Lens EventProcessor BlockStore
  lBlockStore = epBlockStore

  lBlockTree : Lens EventProcessor BlockTree
  lBlockTree = ? -- lBlockStore ∙ bsInner
-}
