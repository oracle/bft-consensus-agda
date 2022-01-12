{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert         as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.BlockInfo                             as BlockInfo
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.LBFT
open import Optics.All
open import Util.Hash
open import Util.Prelude
open import Util.Types
------------------------------------------------------------------------------
open import Data.String                                               using (String)

module LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo where

highestRound : SyncInfo → Round
highestRound self = max (self ^∙ siHighestCertifiedRound) (self ^∙ siHighestTimeoutRound)

verify : SyncInfo → ValidatorVerifier → Either ErrLog Unit

verifyM : SyncInfo → ValidatorVerifier → LBFT (Either ErrLog Unit)
verifyM self validator = pure (verify self validator)

module verify (self : SyncInfo) (validator : ValidatorVerifier) where
  step₀ step₁ step₂ step₃ step₄ step₅ step₆ : Either ErrLog Unit
  here' : List String → List String

  epoch = self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biEpoch

  step₀ = do
    lcheck (epoch == self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biEpoch)
           (here' ("Multi epoch in SyncInfo - HCC and HQC" ∷ []))
    step₁

  step₁ = do
    lcheck (maybeS (self ^∙ siHighestTimeoutCert) true (λ tc -> epoch == tc ^∙ tcEpoch))
           (here' ("Multi epoch in SyncInfo - TC and HQC" ∷ []))
    step₂

  step₂ = do
    lcheck (   self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biRound
           ≥? self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biRound)
           (here' ("HQC has lower round than HCC" ∷ []))
    step₃

  step₃ = do
    lcheck (self ^∙ siHighestCommitCert ∙ qcCommitInfo /= BlockInfo.empty)
           (here' ("HCC has no committed block" ∷ []))
    step₄

  step₄ = do
    QuorumCert.verify (self ^∙ siHighestQuorumCert) validator
    step₅

  step₅ = do
    -- Note: do not use (self ^∙ siHighestCommitCert) because it might be
    -- same as siHighestQuorumCert -- so no need to check again
    maybeS (self ^∙ sixxxHighestCommitCert) (pure unit) (` QuorumCert.verify ` validator)
    step₆

  step₆ = do
    maybeS (self ^∙ siHighestTimeoutCert)   (pure unit) (` TimeoutCertificate.verify ` validator)

  here' t = "SyncInfo" ∷ "verify" ∷ t

verify = verify.step₀

hasNewerCertificates : SyncInfo → SyncInfo → Bool
hasNewerCertificates self other
  = ⌊ self ^∙ siHighestCertifiedRound >? other ^∙ siHighestCertifiedRound ⌋
  ∨ ⌊ self ^∙ siHighestTimeoutRound   >? other ^∙ siHighestTimeoutRound   ⌋
  ∨ ⌊ self ^∙ siHighestCommitRound    >? other ^∙ siHighestCommitRound    ⌋
