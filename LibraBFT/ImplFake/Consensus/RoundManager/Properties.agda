{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.ImplFake.Consensus.RoundManager.Properties where

  open import LibraBFT.ImplFake.Consensus.RoundManager

  voteForCurrentEpoch : ∀ {ts pm pre vm αs}
                      → (SendVote vm αs) ∈ LBFT-outs (processProposalMsg ts pm) pre
                      → (₋rmEC pre) ^∙ rmEpoch ≡ vm ^∙ vmVote ∙ vEpoch
  voteForCurrentEpoch (here refl) = refl

  -- The quorum certificates sent in SyncInfo with votes are those from the peer state.
  -- This is no longer used because matching m∈outs parameters to here refl eliminated the need for
  -- it, at least for our simple handler.  I'm keeping it, though, as it may be needed in future
  -- when the real handler will be much more complicated and this proof may no longer be trivial.
  procPMCerts≡ : ∀ {ts pm pre vm αs}
               → (SendVote vm αs) ∈ LBFT-outs (processProposalMsg ts pm) pre
               → vm ^∙ vmSyncInfo ≡ SyncInfo∙new (₋rmHighestQC pre) (₋rmHighestCommitQC pre)
  procPMCerts≡ (here refl) = refl
