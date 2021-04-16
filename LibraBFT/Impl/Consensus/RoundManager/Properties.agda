{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.RoundManager.Properties
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open import LibraBFT.Impl.Consensus.RoundManager hash hash-cr

  voteForCurrentEpoch : ∀ {ts pm pre vm αs}
                      → (SendVote vm αs) ∈ LBFT-outs (processProposalMsg ts pm) pre
                      → (₋rmamEC pre) ^∙ rmEpoch ≡ vm ^∙ vmVote ∙ vEpoch
  voteForCurrentEpoch (here refl) = refl

  -- The quorum certificates sent in SyncInfo with votes are those from the peer state
  procPMCerts≡ : ∀ {ts pm pre vm αs}
               → (SendVote vm αs) ∈ LBFT-outs (processProposalMsg ts pm) pre
               → vm ^∙ vmSyncInfo ≡ mkSyncInfo (₋rmHighestQC (₋rmamRM pre)) (₋rmHighestCommitQC (₋rmamRM pre))
  procPMCerts≡ (there x)   = ⊥-elim (¬Any[] x)  -- processProposalMsg sends only one vote
  procPMCerts≡ (here refl) = refl
