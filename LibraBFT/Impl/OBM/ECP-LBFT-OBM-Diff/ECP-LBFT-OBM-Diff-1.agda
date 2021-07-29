{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-0 as ECP-LBFT-OBM-Diff-0
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-1 where

------------------------------------------------------------------------------

amIMemberOfCurrentEpoch : Author → List Author → Bool
amIMemberOfCurrentEpochM : LBFT Bool

------------------------------------------------------------------------------

e_RoundState_processLocalTimeoutM : Epoch → Round → LBFT Bool
e_RoundState_processLocalTimeoutM e r =
  if-RWST not ECP-LBFT-OBM-Diff-0.enabled
  then yes'
  else
    -- LBFT-OBM-DIFF : do not broadcast timeouts if not member of epoch
    ifM amIMemberOfCurrentEpochM
        yes'
        (do
          logInfo fakeInfo -- ["not a member of Epoch", "ignoring timeout", lsE e, lsR r]
          pure false)
 where
  yes' : LBFT Bool
  yes' = do
    logInfo fakeInfo -- InfoRoundTimeout e r
    pure true

------------------------------------------------------------------------------

amIMemberOfCurrentEpochM =
  use (lRoundManager ∙ rmObmMe) >>= λ where
    nothing → do
      logErr fakeErr -- no identity
      pure false
    (just me) →
      amIMemberOfCurrentEpoch <$> pure me <*> use (lRoundManager ∙ rmObmAllAuthors)

-- TODO-1 : what is the stdlib function for this?
amIMemberOfCurrentEpoch _ [] = false
amIMemberOfCurrentEpoch x (x' ∷ xs) =
  if x == x' then true else amIMemberOfCurrentEpoch x xs
