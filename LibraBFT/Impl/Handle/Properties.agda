{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

open import LibraBFT.Impl.Properties.Aux  -- TODO-1: maybe Aux properties should be in this file?
open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm (ℓ+1 0ℓ) EpochConfig epochId authorsN ConcSysParms NodeId-PK-OK
open        Structural impl-sps-avp


-- This module provides some scaffolding to define the handlers for our fake/simple "implementation"
-- and connect them to the interface of the SystemModel.

module LibraBFT.Impl.Handle.Properties
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
  open import LibraBFT.Impl.Consensus.ChainedBFT.EventProcessor hash hash-cr
  open import LibraBFT.Impl.Handle hash hash-cr

  ----- Properties that bridge the system model gap to the handler -----

  postulate -- TODO-1: prove
   msgsToSendWereSent1 : ∀ {pid ts pm vm} {st : EventProcessor}
                       → send (V vm) ∈ proj₂ (peerStep (pid , P pm) ts st)
                       → ∃[ αs ] (SendVote vm αs ∈ LBFT-outs (handle (pid , P pm) ts) st)

   msgsToSendWereSent : ∀ {pid ts nm m} {st : EventProcessor}
                      → m ∈ proj₂ (peerStepWrapper pid nm st)
                      → ∃[ vm ] (m ≡ V vm × send (V vm) ∈ proj₂ (peerStep (pid , nm) ts st))
