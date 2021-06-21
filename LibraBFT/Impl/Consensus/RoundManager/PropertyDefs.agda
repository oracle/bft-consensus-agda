{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions of properties of only the behavior of the
-- handlers, nothing concerning the system state.

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util

module LibraBFT.Impl.Consensus.RoundManager.PropertyDefs where

-- The codomain for the property that a vote has been correctly tagged with the
-- source meta-data. The actual statement of the property depends on the
-- stateful computation we are considering (e.g., whether the vote is being
-- returned or emitted as output).

data VoteSrcCorrectCod (pre post : RoundManager) (vote : Vote) : Set where
  mvsNew :      just vote ≡ post ^∙ lSafetyData ∙ sdLastVote → VoteSrcCorrectCod pre post vote
  mvsLastVote : just vote ≡ pre ^∙ lSafetyData ∙ sdLastVote
              → pre ≡L post at (lSafetyData ∙ sdLastVote)    → VoteSrcCorrectCod pre post vote
