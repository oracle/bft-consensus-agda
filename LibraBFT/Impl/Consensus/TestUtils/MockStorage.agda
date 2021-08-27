{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                                  as Map
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.RecoveryData                 as RecoveryData
import      LibraBFT.Impl.Consensus.TestUtils.MockSharedStorage  as MockSharedStorage
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Storage.DiemDB.LedgerStore.LedgerStore as LedgerStore
import      LibraBFT.Impl.Types.LedgerInfo                       as LedgerInfo
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                          as String

module LibraBFT.Impl.Consensus.TestUtils.MockStorage where

------------------------------------------------------------------------------

postulate -- TODO-2: sortOn
  sortOn : (Block → Round) → List Block → List Block

------------------------------------------------------------------------------

start : MockStorage → Either ErrLog RecoveryData

------------------------------------------------------------------------------

newWithLedgerInfo : MockSharedStorage → LedgerInfo → MockStorage
newWithLedgerInfo sharedStorage ledgerInfo =
  let li  = if ledgerInfo ^∙ liEndsEpoch
            then ledgerInfo
            else LedgerInfo.mockGenesis (just (sharedStorage ^∙ mssValidatorSet))
      lis = LedgerInfoWithSignatures∙new li Map.empty
   in MockStorage∙new
      (sharedStorage & mssLis %~ Map.insert (lis ^∙ liwsLedgerInfo ∙ liVersion) lis)
      li
      (DiemDB∙new LedgerStore.new)

getLedgerRecoveryData : MockStorage → LedgerRecoveryData
getLedgerRecoveryData self =
  LedgerRecoveryData∙new (self ^∙ msStorageLedger)

tryStart : MockStorage → Either ErrLog RecoveryData
tryStart self =
  withErrCtx' (here' []) $
  RecoveryData.new
    (self ^∙ msSharedStorage ∙ mssLastVote)
    (getLedgerRecoveryData self)
    (sortOn (_^∙ bRound) (Map.elems (self ^∙ msSharedStorage ∙ mssBlock)))
    RootMetadata∙new
    (Map.elems (self ^∙ msSharedStorage ∙ mssQc))
    (self ^∙ msSharedStorage ∙ mssHighestTimeoutCertificate)
 where
  here' : List String.String → List String.String
  here' t = "MockStorage" ∷ "tryStart" ∷ t

startForTesting : ValidatorSet → Maybe LedgerInfoWithSignatures
                → Either ErrLog (RecoveryData × PersistentLivenessStorage)
startForTesting validatorSet obmMLIWS = do
  let (sharedStorage , genesisLi) = case obmMLIWS of λ where
        nothing     → ( MockSharedStorage.new            validatorSet
                      , LedgerInfo.mockGenesis     (just validatorSet) )
        (just liws) → ( MockSharedStorage.newObmWithLIWS validatorSet liws
                      , liws ^∙ liwsLedgerInfo )
      storage = newWithLedgerInfo sharedStorage genesisLi
  ss ← withErrCtx' (here' []) (start storage)
  pure (ss , storage)
 where
  here' : List String.String → List String.String
  here' t = "MockStorage" ∷ "startForTesting" ∷ t

------------------------------------------------------------------------------

saveTreeE
  : List Block → List QuorumCert → MockStorage
  → Either ErrLog MockStorage

saveTreeM
  : List Block → List QuorumCert → MockStorage
  → LBFT (Either ErrLog MockStorage)
saveTreeM bs qcs db = do
  logInfo fakeInfo -- [ "MockStorage", "saveTreeM", show (length bs), show (length qcs) ]
  pure (saveTreeE bs qcs db)

saveTreeE bs qcs db =
  pure (db & msSharedStorage ∙ mssBlock %~ insertBs
           & msSharedStorage ∙ mssQc    %~ insertQCs)
 where
  insertBs : Map.KVMap HashValue Block → Map.KVMap HashValue Block
  insertBs  m = foldl' (λ acc b  → Map.insert (b ^∙ bId)                      b  acc) m bs

  insertQCs : Map.KVMap HashValue QuorumCert → Map.KVMap HashValue QuorumCert
  insertQCs m = foldl' (λ acc qc → Map.insert (qc ^∙ qcCertifiedBlock ∙ biId) qc acc) m qcs

pruneTreeM
  : List HashValue → MockStorage
  → LBFT (Either ErrLog MockStorage)
pruneTreeM ids db = do
  logInfo fakeInfo -- ["MockStorage", "pruneTreeM", show (fmap lsHV ids)]
  ok (db & msSharedStorage ∙ mssBlock %~ deleteBs
         & msSharedStorage ∙ mssQc    %~ deleteQCs)
  -- TODO : verifyConsistency
 where
  deleteBs : Map.KVMap HashValue Block → Map.KVMap HashValue Block
  deleteBs  m = foldl' (flip Map.delete) m ids

  deleteQCs : Map.KVMap HashValue QuorumCert → Map.KVMap HashValue QuorumCert
  deleteQCs m = foldl' (flip Map.delete) m ids

saveStateM
  : Vote → MockStorage
  → LBFT (Either ErrLog MockStorage)
saveStateM v db = do
  logInfo fakeInfo -- ["MockStorage", "saveStateM", lsV v]
  ok (db & msSharedStorage ∙ mssLastVote ?~ v)

start  = tryStart

saveHighestTimeoutCertificateM
  : TimeoutCertificate → MockStorage
  → LBFT (Either ErrLog MockStorage)
saveHighestTimeoutCertificateM tc db = do
  logInfo fakeInfo -- ["MockStorage", "saveHighestTimeoutCertificateM", lsTC tc]
  ok (db & msSharedStorage ∙ mssHighestTimeoutCertificate ?~ tc)

retrieveEpochChangeProofE
  : Version → MockStorage
  → Either ErrLog EpochChangeProof
retrieveEpochChangeProofE v db = case Map.lookup v (db ^∙ msSharedStorage ∙ mssLis) of λ where
  nothing    → Left fakeErr -- ["MockStorage", "retrieveEpochChangeProofE", "not found", show v])
  (just lis) → pure (EpochChangeProof∙new (lis ∷ []) false)
