{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-2 as ECP-LBFT-OBM-Diff-2
import      LibraBFT.Impl.Storage.DiemDB.LedgerStore.LedgerStore    as LedgerStore
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD
open import LibraBFT.ImplShared.Util.Dijkstra.EitherD.Syntax
open import LibraBFT.ImplShared.Util.Dijkstra.Syntax
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Storage.DiemDB.DiemDB where

------------------------------------------------------------------------------
getEpochEndingLedgerInfosImpl
  : DiemDB → Epoch → Epoch → Epoch {-Usize-}
  → Either ErrLog (List LedgerInfoWithSignatures × Bool)
getLatestLedgerInfo
  : DiemDB
  → Either ErrLog LedgerInfoWithSignatures
------------------------------------------------------------------------------

mAX_NUM_EPOCH_ENDING_LEDGER_INFO : Epoch -- Usize
mAX_NUM_EPOCH_ENDING_LEDGER_INFO = 100

------------------------------------------------------------------------------
-- impl DiemDB

-- Returns ledger infos for epoch changes starting with the given epoch.
-- If there are less than `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results, it returns all of them.
-- Otherwise the first `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results are returned
-- and a flag is set to True to indicate there are more.
getEpochEndingLedgerInfos
  : DiemDB → Epoch → Epoch
    → Either ErrLog (List LedgerInfoWithSignatures × Bool)
getEpochEndingLedgerInfos self startEpoch endEpoch =
  getEpochEndingLedgerInfosImpl self startEpoch endEpoch mAX_NUM_EPOCH_ENDING_LEDGER_INFO

-- TODO-2: provide EitherD variants before writing proofs about this function;
-- at that time, use `whenD` in place of the two `if`s below
getEpochEndingLedgerInfosImpl self startEpoch endEpoch limit = do
  if (not ⌊ (startEpoch ≤? endEpoch) ⌋)
    then
    (Left fakeErr {-here ["bad epoch range", lsE startEpoch, lsE endEpoch]-})
    else pure unit
  -- the latest epoch can be the same as the current epoch (in most cases), or
  -- current_epoch + 1 (when the latest ledger_info carries next validator set)
  latestEpoch ← getLatestLedgerInfo self >>= pure ∘ (_^∙  liwsLedgerInfo ∙ liNextBlockEpoch)
  if (not ⌊ (endEpoch ≤? latestEpoch) ⌋)
    then
    (Left fakeErr) -- [ "unable to provide epoch change ledger info for still open epoch"
                   -- , "asked upper bound", lsE endEpoch
                   -- , "last sealed epoch", lsE (latestEpoch - 1) ])))
                   -- -1 is OK because genesis LedgerInfo has .next_block_epoch() == 1
    else pure unit

  let (pagingEpoch , more) =
        ECP-LBFT-OBM-Diff-2.e_DiemDB_getEpochEndingLedgerInfosImpl_limit startEpoch endEpoch limit
  lis0    ← LedgerStore.getEpochEndingLedgerInfoIter (self ^∙ ddbLedgerStore) startEpoch pagingEpoch
  let lis = LedgerStore.obmEELIICollect lis0
  if length lis + (startEpoch {-^∙ eEpoch-}) /= (pagingEpoch {-^∙ eEpoch-})
    then Left fakeErr -- [ "DB corruption: missing epoch ending ledger info"
                      -- , lsE startEpoch, lsE endEpoch, lsE pagingEpoch ]
    else pure (lis , more)
{-
 where
  here t = "DiemDB":"getEpochEndingLedgerInfosImpl":t
-}

------------------------------------------------------------------------------

-- impl DbReader for DiemDB

getLatestLedgerInfo self =
  maybeS (self ^∙ ddbLedgerStore ∙ lsLatestLedgerInfo)
         (Left fakeErr {-["DiemDB.Lib", "getLatestLedgerInfo", "Nothing"]-})
         pure

getEpochEndingLedgerInfo : DiemDB → Version → Either ErrLog LedgerInfoWithSignatures
getEpochEndingLedgerInfo = LedgerStore.getEpochEndingLedgerInfo ∘ _ddbLedgerStore

------------------------------------------------------------------------------

-- impl DbWriter for DiemDB

-- LBFT-OBM-DIFF : entire impl
module saveTransactions (self  : DiemDB)
                        {- → [TransactionToCommit] → Version-}
                        (mliws : Maybe LedgerInfoWithSignatures) where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL = EL ErrLog DiemDB

  step₁ : LedgerInfoWithSignatures               → VariantFor EitherD
  step₂ : LedgerInfoWithSignatures → LedgerStore → VariantFor EitherD

  step₀ : VariantFor EitherD
  step₀ = maybeSD mliws (LeftD fakeErr) step₁

  step₁ liws =
    eitherSD (LedgerStore.putLedgerInfo (self ^∙ ddbLedgerStore) liws) LeftD (step₂ liws)

  step₂ liws ls =
    RightD (self & ddbLedgerStore ∙~ (ls & lsLatestLedgerInfo ?~ liws))

  E : VariantFor Either
  E = toEither step₀

  D : VariantFor EitherD
  D = fromEither E

saveTransactions = saveTransactions.D
