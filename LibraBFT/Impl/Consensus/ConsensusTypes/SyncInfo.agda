{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo where

highestRound : SyncInfo → Round
highestRound self = max (self ^∙ siHighestCertifiedRound) (self ^∙ siHighestTimeoutRound)

postulate
  verifyM : SyncInfo → ValidatorVerifier → LBFT (Either ErrLog Unit)

hasNewerCertificates : SyncInfo → SyncInfo → Bool
hasNewerCertificates self other
  = ⌊ self ^∙ siHighestCertifiedRound >? other ^∙ siHighestCertifiedRound ⌋
  ∨ ⌊ self ^∙ siHighestTimeoutRound   >? other ^∙ siHighestTimeoutRound   ⌋
  ∨ ⌊ self ^∙ siHighestCommitRound    >? other ^∙ siHighestCommitRound    ⌋
