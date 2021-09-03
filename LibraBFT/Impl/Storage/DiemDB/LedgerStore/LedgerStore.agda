{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Base.KVMap                 as Map
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types hiding (getEpoch)
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                         using (String)

module LibraBFT.Impl.Storage.DiemDB.LedgerStore.LedgerStore where

record EpochEndingLedgerInfoIter : Set where
  constructor EpochEndingLedgerInfoIter∙new
  field
    _eeliiObmLIWS : List LedgerInfoWithSignatures
open EpochEndingLedgerInfoIter public

new : LedgerStore
new = mkLedgerStore Map.empty Map.empty nothing

-- OBM-LBFT-DIFF : this entire impl file is VERY different

getEpoch : LedgerStore → Version → Either ErrLog Epoch
getEpoch self version =
  maybeS (Map.lookup version (self ^∙ lsObmVersionToEpoch))
         -- COMMENT FROM RUST CODE:
         -- There should be a genesis LedgerInfo at version 0.
         -- This normally doesn't happen.
         -- This part of impl does not need to rely on this assumption.
         (pure 0)
         pure

getEpochEndingLedgerInfo : LedgerStore → Version → Either ErrLog LedgerInfoWithSignatures
getEpochEndingLedgerInfo self version = do
  epoch ← getEpoch self version
  case Map.lookup epoch (self ^∙ lsObmEpochToLIWS) of λ where
    nothing   → Left fakeErr -- ["DiemDbError::NotFound", "LedgerInfo for epoch", lsE epoch]
    (just li) →
      grd‖ li ^∙ liwsLedgerInfo ∙ liVersion /= version ≔
           Left fakeErr --["epoch did not end at version", lsE epoch, lsVersion version]
         ‖ is-nothing (li ^∙ liwsLedgerInfo ∙ liNextEpochState) ≔
           Left fakeErr -- ["not an epoch change at version", lsVersion version]
         ‖ otherwise≔
           pure li
--where
-- here t = "LedgerStore":"getEpochEndingLedgerInfo":t

getEpochState : LedgerStore → Epoch → Either ErrLog EpochState
getEpochState self epoch = do
  lcheck (epoch >? 0) (here' ("EpochState only queryable for epoch >= 1" {-∷ lsE epoch-} ∷ []))
  case Map.lookup (epoch ∸ 1) (self ^∙ lsObmEpochToLIWS) of λ where
    nothing → Left fakeErr --[ "DiemDbError::NotFound"
                           --, "last LedgerInfo of epoch", lsE (epoch - 1) ]))
    (just ledgerInfoWithSigs) →
      maybeS (ledgerInfoWithSigs ^∙ liwsNextEpochState)
             (Left fakeErr) --[ "last LedgerInfo in epoch must carry nextEpochState"
                            --, lsE epoch, lsLI (ledgerInfoWithSigs^.liwsLedgerInfo) ]
             pure
 where
  here' : List String → List String
  here' t = "LedgerStore" ∷ "getEPochState" ∷ t

-- iterator that yields epoch ending ledger infos
-- starting from `start_epoch`
-- ends at the one before `end_epoch`
getEpochEndingLedgerInfoIter
  : LedgerStore → Epoch → Epoch
  → Either ErrLog EpochEndingLedgerInfoIter
getEpochEndingLedgerInfoIter self startEpoch endEpoch =
  -- TODO-2: prove endEpoch > 0
  -- Use of monus in context where it is not clear that endEpoch > 0.
  -- If not, Agda and Haskell code would behave differently.
  -- TODO-2: IMPL-DIFF: Haskell uses a list comprehension; Agda uses homegrown 'fromToList'
  -- The combination of monus and fromToList risks misunderstanding/misuse of fromToList later.
  -- Ranges would differ in Haskell and Agda if, say, startEpoch were negative and endEpoch was 0.
  -- It could be correct and verified in Agda, but wrong in Haskell
  -- (e.g., if the Haskell code accidentally calculates a negative epoch).
  EpochEndingLedgerInfoIter∙new <$> (foldM) go [] (fromToList startEpoch (endEpoch ∸ 1))
 where
  go : List LedgerInfoWithSignatures → Epoch → Either ErrLog (List LedgerInfoWithSignatures)
  go acc e = maybeS (Map.lookup e (self ^∙ lsObmEpochToLIWS))
                    (Left fakeErr) --[ "LedgerStore", "getEpochEndingLedgerInfoIter"
                                   --, "no LIWS for epoch", lsE e ]
                    (λ x → Right (acc ++ (x ∷ []))) -- TODO

putLedgerInfo : LedgerStore → LedgerInfoWithSignatures → Either ErrLog LedgerStore
putLedgerInfo self ledgerInfoWithSigs =
  let ledgerInfo = ledgerInfoWithSigs ^∙ liwsLedgerInfo
   in pure
    $ mkLedgerStore
      ((if ledgerInfo ^∙ liEndsEpoch
         then Map.insert (ledgerInfo ^∙ liVersion) (ledgerInfo ^∙ liEpoch)
         else identity)
       (self ^∙ lsObmVersionToEpoch))
      (Map.insert (ledgerInfo ^∙ liEpoch) ledgerInfoWithSigs
       (self ^∙ lsObmEpochToLIWS))
      (self ^∙ lsLatestLedgerInfo)

obmEELIICollect : EpochEndingLedgerInfoIter → List LedgerInfoWithSignatures
obmEELIICollect = _eeliiObmLIWS
