{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.VoteMsg where

verify : VoteMsg → ValidatorVerifier → Either ErrLog Unit
verify self validator = do
-- lcheck (self ^∙ vmVote ∙ vEpoch == self ^∙ vmSyncInfo ∙ siEpoch)
--        (here $ "VoteMsg has different epoch" ∷ lsSI (self ^∙ vmSyncInfo) ∷ [])
  Vote.verify (self ^∙ vmVote) validator
