{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                   as Map
open import LibraBFT.Base.PKCS                    hiding (verify)
open import LibraBFT.Impl.OBM.Crypto              hiding (verify)
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.ValidatorVerifier as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate where

verify : TimeoutCertificate → ValidatorVerifier → Either ErrLog Unit
verify self validator =
  withErrCtx' ("TimeoutCertificate" ∷ "verify" ∷ "failed" ∷ [])
  (ValidatorVerifier.verifyAggregatedStructSignature
    validator (self ^∙ tcTimeout) (self ^∙ tcSignatures))

verify' : Maybe TimeoutCertificate → ValidatorVerifier → Either ErrLog Unit
verify' mtc validator = maybeSMP (pure mtc) unit (` verify ` validator)

-- HC-TODO : refactor this and LedgerInfoWithSignatures
addSignature : Author → Signature → TimeoutCertificate → TimeoutCertificate
addSignature a s tc =
  case Map.lookup a (tc ^∙ tcSignatures) of λ where
    (just _) → tc
    nothing  → tc & tcSignatures ∙~ Map.kvm-insert-Haskell a s (tc ^∙ tcSignatures)
