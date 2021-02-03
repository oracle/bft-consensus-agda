{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS

open import LibraBFT.Abstract.Types
open EpochConfig

open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr

open import LibraBFT.Concrete.System.Parameters

open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.AvailableEpochs using (AvailableEpochs ; lookup'; lookup'')
open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms

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
   open PerState st r
   open PerEpoch eid

   open import LibraBFT.Abstract.Obligations.LockedRound 𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔) as LR

   postulate  -- TODO-3: prove it
     lrr : LR.Type IntSystemState
