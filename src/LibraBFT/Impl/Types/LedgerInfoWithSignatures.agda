{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.OBM.Crypto              as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Types.ValidatorVerifier as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
import      Util.KVMap                   as Map
open import Util.PKCS
open import Util.Prelude

module LibraBFT.Impl.Types.LedgerInfoWithSignatures where

obmNewNoSigs : LedgerInfo → LedgerInfoWithSignatures
obmNewNoSigs li = LedgerInfoWithSignatures∙new li Map.empty

-- HC-TODO : refactor this and TimeoutCertificate
addSignature : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addSignature validator sig liws =
  case Map.lookup validator (liws ^∙ liwsSignatures) of λ where
    (just _) → liws
    nothing  →
      liws & liwsSignatures ∙~ Map.kvm-insert-Haskell validator sig (liws ^∙ liwsSignatures)

verifySignatures : LedgerInfoWithSignatures → ValidatorVerifier → Either ErrLog Unit
verifySignatures self validator = withErrCtx'
  ("LedgerInfoWithSignatures" ∷ "verify" ∷ [])
  (ValidatorVerifier.batchVerifyAggregatedSignatures
     validator (self ^∙ liwsLedgerInfo) (self ^∙ liwsSignatures))

