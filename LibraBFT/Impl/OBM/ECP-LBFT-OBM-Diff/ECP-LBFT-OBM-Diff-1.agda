{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-0 as ECP-LBFT-OBM-Diff-0
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Storage.DiemDB.DiemDB                     as DiemDB
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
  ifD not ECP-LBFT-OBM-Diff-0.enabled
  then yes'
  else
    -- LBFT-OBM-DIFF : do not broadcast timeouts if not member of epoch
    ifMD amIMemberOfCurrentEpochM
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

postulate
 e_EpochManager_doECP_waitForRlec
  : EpochManager → EpochChangeProof
  → Either ErrLog Bool

------------------------------------------------------------------------------

e_EpochManager_startNewEpoch
  : EpochManager → EpochChangeProof
  → Either ErrLog EpochManager
e_EpochManager_startNewEpoch self ecp =
  if not ECP-LBFT-OBM-Diff-0.enabled
  then pure self
  else do
    -- LBFT-OBM-DIFF: store all the epoch ending LedgerInfos sent in ECP
    -- (to avoid gaps -- from when a node is not a member).
    db <- (foldM) (\db l → DiemDB.saveTransactions db (just l))
                  (self ^∙ emStorage ∙ msObmDiemDB)
                  (ecp ^∙ ecpLedgerInfoWithSigs)
    pure (self & emStorage ∙ msObmDiemDB ∙~ db)

------------------------------------------------------------------------------

postulate
 e_EpochManager_checkEpc
  : EpochManager → EpochChangeProof
  → Either ErrLog Unit

------------------------------------------------------------------------------

postulate
 e_EpochManager_processMessage_ISyncInfo
  : EpochManager → SyncInfo
  → Either ErrLog Unit

------------------------------------------------------------------------------

amIMemberOfCurrentEpochM =
  use (lRoundManager ∙ rmObmMe) >>= λ where
    nothing → do
      logErr fakeErr -- no identity
      pure false
    (just me) →
      amIMemberOfCurrentEpoch <$> pure me <*> use (lRoundManager ∙ rmObmAllAuthors)

amIMemberOfCurrentEpoch = elem
