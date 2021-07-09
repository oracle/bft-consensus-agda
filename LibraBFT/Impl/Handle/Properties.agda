{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

-- This module provides some scaffolding to define the handlers for our
-- implementation and connect them to the interface of the SystemModel.

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK

open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

module LibraBFT.Impl.Handle.Properties where

esEpoch≡sdEpoch
  : ∀ pid (pre : SystemState)
    → ReachableSystemState pre
    → rmGetEpochState (peerStates pre pid) ^∙ esEpoch ≡ (peerStates pre pid) ^∙ lSafetyData ∙ sdEpoch
esEpoch≡sdEpoch pid pre@._ step-0 = refl
esEpoch≡sdEpoch pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-cheat{pid'} cheatMsgConstraint)))
  rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre'} step unit
  = esEpoch≡sdEpoch pid pre' preach
esEpoch≡sdEpoch pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates{pre = pre'} sps pid≢pid')
  = esEpoch≡sdEpoch pid pre' preach
...| yes refl
  with sps
... | step-init ini
  rewrite override-target-≡{a = pid}{b = initRM}{f = peerStates pre'}
  = refl
... | step-msg {fst , P pm} m∈pool ini
  with handleProposalSpec.contract!-NoEpochChange 0 pm (peerStates pre' pid)
... | mkNoEpochChange es≡₁ es≡₂
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  = trans (sym es≡₁) (trans (esEpoch≡sdEpoch pid pre' preach) es≡₂)
esEpoch≡sdEpoch pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} _)))
  | yes refl | step-msg {fst , V x} m∈pool ini = {!!}
esEpoch≡sdEpoch pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} _)))
  | yes refl | step-msg {fst , C x} m∈pool ini = {!!}

-- TODO-3: Prove this
postulate
  impl-sps-avp : StepPeerState-AllValidParts
