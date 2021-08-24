{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Consensus.Types

module LibraBFT.Impl.IO.OBM.ObmNeedFetch where

{-
TODO-1 : add comments about this module.
-}

postulate -- TODO-1: writeRequestReadResponseUNSAFE
  writeRequestReadResponseUNSAFE
    : ObmNeedFetch → Author → Author → BlockRetrievalRequest
    → BlockRetrievalResponse


