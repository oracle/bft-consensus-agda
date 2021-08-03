{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert         as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.BlockInfo                             as BlockInfo
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                         as String

module LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo where

highestRound : SyncInfo → Round
highestRound self = max (self ^∙ siHighestCertifiedRound) (self ^∙ siHighestTimeoutRound)

verify : SyncInfo → ValidatorVerifier → Either ErrLog Unit

verifyM : SyncInfo → ValidatorVerifier → LBFT (Either ErrLog Unit)
verifyM self validator = pure (verify self validator)

verify self validator = do
  let epoch      = self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biEpoch

  lcheck (epoch == self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biEpoch)
         (here' ("Multi epoch in SyncInfo - HCC and HQC" ∷ []))

  lcheck (maybeS (self ^∙ siHighestTimeoutCert) true (λ tc -> epoch == tc ^∙ tcEpoch))
         (here' ("Multi epoch in SyncInfo - TC and HQC" ∷ []))

  lcheck (   self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biRound
          ≥? self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biRound)
         (here' ("HQC has lower round than HCC" ∷ []))

  lcheck (self ^∙ siHighestCommitCert ∙ qcCommitInfo /= BlockInfo.empty)
         (here' ("HCC has no committed block" ∷ []))

  QuorumCert.verify (self ^∙ siHighestQuorumCert) validator

  -- Note: do not use (self ^∙ siHighestCommitCert) because it might be
  -- same as siHighestQuorumCert -- so no need to check again
  maybeS (self ^∙ sixxxHighestCommitCert) (pure unit) (λ qc → QuorumCert.verify qc validator)

  maybeS (self ^∙ siHighestTimeoutCert)   (pure unit) (λ tc → TimeoutCertificate.verify tc validator)
 where
  here' : List String.String → List String.String
  here' t = "SyncInfo" ∷ "verify" ∷ t

hasNewerCertificates : SyncInfo → SyncInfo → Bool
hasNewerCertificates self other
  = ⌊ self ^∙ siHighestCertifiedRound >? other ^∙ siHighestCertifiedRound ⌋
  ∨ ⌊ self ^∙ siHighestTimeoutRound   >? other ^∙ siHighestTimeoutRound   ⌋
  ∨ ⌊ self ^∙ siHighestCommitRound    >? other ^∙ siHighestCommitRound    ⌋
