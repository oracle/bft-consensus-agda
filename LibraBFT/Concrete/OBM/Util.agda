open import LibraBFT.Prelude

module LibraBFT.Concrete.OBM.Util where

  open import LibraBFT.Concrete.OBM.RWST public
  open import LibraBFT.Concrete.Consensus.Types

  ----------------
  -- LBFT Monad --
  ----------------
 
  LBFT : Set → Set
  LBFT = RWST Unit Action EventProcessor