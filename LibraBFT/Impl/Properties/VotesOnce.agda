{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.Common    as Common
import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.ImplFake.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState.

module LibraBFT.Impl.Properties.VotesOnce (𝓔 : EpochConfig) where

peerCanSign-Msb4
  : ∀ {pid v pk}{pre post : SystemState}
    → ReachableSystemState pre
    → Step pre post
    → PeerCanSignForPK post v pid pk
    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → PeerCanSignForPK pre v pid pk
peerCanSign-Msb4 = {!!}

oldVoteRound≤lvr
  : ∀ {pid pk v}{pre : SystemState}
    → (r : ReachableSystemState pre)
    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
    → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → PeerCanSignForPK pre v pid pk
    → (_rmEC (peerStates pre pid)) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
    → v ^∙ vRound ≤ (_rmEC (peerStates pre pid)) ^∙ rmLastVotedRound
oldVoteRound≤lvr = {!!}

peerLastVoteSentB4
  : ∀ {pre pid v pk}
    → ReachableSystemState pre
    → just v ≡ (peerStates pre pid ^∙ (lSafetyData ∙ sdLastVote))
    → (sig : WithVerSig pk v)
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
peerLastVoteSentB4 preach lvr sig = {!!}

votesOnce₁ : Common.IncreasingRoundObligation InitAndHandlers 𝓔
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini){v}{m}{v'}{m'} hpk v⊂m m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡
   with RWST-contract (handleProposal 0 pm)
          (handleProposalSpec.Contract 0 pm (peerStates pre pid)) unit (peerStates pre pid)
          (handleProposalSpec.contract 0 pm (peerStates pre pid))
... | Left msgs≡[] = ⊥-elim (send∉actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} msgs≡[] m∈outs)
... | Right (vm , pid-proposer , handleProposalSpec.mkContract-HasOuts msgs≡ ep≡ lvr-pre lvr-post)
   with sendV∈actions{vm}{pid-proposer ∷ []}{LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym msgs≡) m∈outs
... | refl
   with v⊂m
... | vote∈qc vs∈qc v≈rbld (inV qc∈m) = {!!}
... | vote∈vm
   with ⊎-elimʳ ¬msb (impl-sps-avp preach hpk sps m∈outs v⊂m sig ¬gen)
... | vspkv , _
    with lvr-pre
...| inj₁ lvr<vr =
  let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl
      vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
      step   = step-peer (step-honest sps)
      vspre' = peerCanSign-Msb4 preach step vspkv' hpk sig' m'mwsb
      rv'<rv = oldVoteRound≤lvr preach hpk sig' ¬gen' m'mwsb vspre' (trans (trans {!!} ep≡) eid≡) in
  inj₁ (≤-trans (s≤s rv'<rv) lvr<vr)
...| inj₂ sdlv≡v = ⊥-elim (¬msb (peerLastVoteSentB4 preach sdlv≡v sig))

votesOnce₁ {pid = pid} {pid'} {pre = pre} preach sps@(step-msg {sndr , V m} m∈pool ini) {v = v} {v' = v'} hpk v⊂m m∈outs sig ¬gen ¬msb v'⊂m' m'∈pool sig' ¬gen' eid≡ r≡ = {!!}
