{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap           as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.LedgerInfoWithSignatures where

-- HC-TODO : refactor this and TimeoutCertificate
addSignature : AccountAddress → Signature → LedgerInfoWithSignatures → LedgerInfoWithSignatures
addSignature validator sig liws =
  case Map.lookup validator (liws ^∙ liwsSignatures) of λ where
    (just _) → liws
    nothing  →
      liws & liwsSignatures ∙~ Map.kvm-insert-Haskell validator sig (liws ^∙ liwsSignatures)



