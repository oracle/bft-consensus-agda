{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                 as Map
open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.TestUtils.MockStorage where

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
