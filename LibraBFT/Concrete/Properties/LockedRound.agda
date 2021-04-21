{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm (ℓ+1 0ℓ) EpochConfig epoch authorsN ConcSysParms NodeId-PK-OK

-- This module contains placeholders for the future analog of the
-- corresponding VotesOnce property.  Defining the implementation
-- obligation and proving that it is an invariant of an implementation
-- is a substantial undertaking.  We are working first on proving the
-- simpler VotesOnce property to settle down the structural aspects
-- before tackling the harder semantic issues.
module LibraBFT.Concrete.Properties.LockedRound where
 -- TODO-3: define the implementation obligation
 ImplObligation₁ : Set
 ImplObligation₁ = Unit

 -- Next, we prove that given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-LR1 : ImplObligation₁)
   where
  -- Any reachable state satisfies the LR rule for any epoch in the system.
  module _ {e}(st : SystemState e)(r : ReachableSystemState st)(eid : Fin e) where
   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr

   -- Bring in IntSystemState
   open import LibraBFT.Concrete.System sps-corr
   open        PerState st r
   open        PerEpoch eid
   open import LibraBFT.Concrete.Obligations.LockedRound 𝓔 (ConcreteVoteEvidence 𝓔) as LR

   postulate  -- TODO-3: prove it
     lrr : LR.Type IntSystemState
