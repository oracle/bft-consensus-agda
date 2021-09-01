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

module getEpochEndingLedgerInfos where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL =
    DiemDB → Epoch → Epoch
    → EL ErrLog (List LedgerInfoWithSignatures × Bool)

  postulate -- TODO-1: getEpochEndingLedgerInfos
    step₀ : VariantFor EitherD

  E : VariantFor Either
  E db ep = toEither ∘ step₀ db ep

  D : VariantFor EitherD
  D db ep = fromEither ∘ E db ep

getEpochEndingLedgerInfos = getEpochEndingLedgerInfos.E

-- TODO-2: hook this up with above
-- Returns ledger infos for epoch changes starting with the given epoch.
-- If there are less than `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results, it returns all of them.
-- Otherwise the first `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results are returned
-- and a flag is set to True to indicate there are more.
getEpochEndingLedgerInfosX
  : DiemDB → Epoch → Epoch
  → Either ErrLog (List LedgerInfoWithSignatures × Bool)
getEpochEndingLedgerInfosX self startEpoch endEpoch =
  getEpochEndingLedgerInfosImpl self startEpoch endEpoch mAX_NUM_EPOCH_ENDING_LEDGER_INFO

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
  if length lis /= (pagingEpoch {-^∙ eEpoch-}) ∸ (startEpoch {-^∙ eEpoch-})
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

module saveTransactions where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL =
    DiemDB {- → [TransactionToCommit] → Version-} → Maybe LedgerInfoWithSignatures
    → EL ErrLog DiemDB

  postulate -- TODO-1: saveTransactions
    step₀ : VariantFor EitherD

  E : VariantFor Either
  E db = toEither ∘ step₀ db

  D : VariantFor EitherD
  D db = fromEither ∘ E db

saveTransactions = saveTransactions.D

-- TODO-2: hook this up with above
-- `first_version` is the version of the first transaction in `txns_to_commit`.
-- When `ledger_info_with_sigs` is provided, verify that the transaction accumulator root hash
-- it carries is generated after the `txns_to_commit` are applied.
-- Note that even if `txns_to_commit` is empty, `frist_version` is checked to be
-- `ledger_info_with_sigs.ledger_info.version + 1` if `ledger_info_with_sigs` is not `None`.
-- LBFT-OBM-DIFF : entire impl
saveTransactionsX
  : DiemDB {- → [TransactionToCommit] → Version-} → Maybe LedgerInfoWithSignatures
  → Either ErrLog DiemDB
saveTransactionsX self {- txnsToCommit firstVersion-} = λ where
  nothing     → pure self
  (just liws) → do
    ls <- LedgerStore.putLedgerInfo (self ^∙ ddbLedgerStore) liws
    pure (self & ddbLedgerStore ∙~ (ls & lsLatestLedgerInfo ?~ liws))




