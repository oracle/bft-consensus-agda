open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types

module LibraBFT.Concrete.OBM.Util where

  open import LibraBFT.Concrete.OBM.RWST public
  
  ----------------
  -- LBFT Monad --
  ----------------
 
  -- Local 'LBFT' monad; which operates only over the part of
  -- the state that /depends/ on the ec; not the part
  -- of the state that /defines/ the ec.
  --
  -- This is very convenient to define functions that
  -- do not alter the ec.
  LBFT-ec : Meta EpochConfig → Set → Set
  LBFT-ec ec = RWST Unit Action (EventProcessorWithEC ec)

  -- Global 'LBFT'; works over the whole state.
  LBFT : Set → Set
  LBFT = RWST Unit Action EventProcessor

  -- Lifting a function that does not alter the pieces that
  -- define the epoch config is easy
  liftEC : {A : Set}(f : ∀ ec → LBFT-ec ec A) → LBFT A
  liftEC f = rwst λ _ st 
    → let ec                 = α-EC (₋epEC st , ₋epEC-correct st)
          res , stec' , acts = RWST-run (f ec) unit (₋epWithEC st)
       in res , record st { ₋epWithEC = stec' } , acts
