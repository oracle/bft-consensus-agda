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
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.ImplFake.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState.

module LibraBFT.Impl.Properties.VotesOnce (𝓔 : EpochConfig) where

-- TODO-3: Prove these
postulate
  peerCanSign-Msb4
    : ∀ {pid v pk}{pre post : SystemState}
      → ReachableSystemState pre
      → Step pre post
      → PeerCanSignForPK post v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk

  -- NOTE: This lemma might very well be useless! `rmLastVotedRound` is a bad
  -- upper bound to use, since it can increase well beyond the round in which a
  -- vote was last generated (let alone sent).
  oldVoteRound≤lvr
    : ∀ {pid pk v}{pre : SystemState}
      → (r : ReachableSystemState pre)
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk
      → (peerStates pre pid) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
      → v ^∙ vRound ≤ (peerStates pre pid) ^∙ rmLastVotedRound

  -- NOTE: A vote being stored in `sdLastVote` does /not/ mean the vote has been
  -- sent, since the peer could have failed to save that vote in its persistent
  -- storage, leading it to drop the vote. We must additionally require that a
  -- vote for the same round as the `sdLastVote`, sent by the same peer, already
  -- exists in the pool.
  peerLastVoteSentB4
    : ∀ {pre pid v m' v' pk}
      → ReachableSystemState pre
      → just v ≡ (peerStates pre pid ^∙ (lSafetyData ∙ sdLastVote))
      → Meta-Honest-PK pk
      → (sig : WithVerSig pk v)
      → v' ⊂Msg m' → (pid , m') ∈ msgPool pre
      → v ≡L v' at vRound
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)

votesOnce₁ : Common.IncreasingRoundObligation InitAndHandlers 𝓔
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {m} {v'} {m'} hpk (vote∈qc x x₁ x₂) m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡ = {!!}
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {.(V (VoteMsg∙new v _))} {v'} {m'} hpk vote∈vm m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡
  with handleProposalSpec.contract! 0 pm (peerStates pre pid)
... | handleProposalSpec.mkContract rmInv noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?) =
  ⊥-elim (sendVote∉actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym noVoteMsgOuts) m∈outs)
... | handleProposalSpec.mkContract rmInv noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid₁ voteMsgOuts vgCorrect)) sdEpoch≡?)
  with sendVote∈actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym voteMsgOuts) m∈outs
... | refl
  with pid ≟ pid'
... | no  pid≢pid' = {!!}
... | yes refl
  with ⊎-elimʳ ¬msb (impl-sps-avp preach hpk sps m∈outs vote∈vm sig ¬gen)
... | vspkv , _ =
  let m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl
      vspkv' = peerCanSignEp≡ {v' = v'} vspkv eid≡
      step   = step-peer (step-honest sps)
      vspre' = peerCanSign-Msb4 preach step vspkv' hpk sig' m'mwsb
      rv'<rv = oldVoteRound≤lvr preach hpk sig' ¬gen' m'mwsb vspre' (esEpoch≡v'Epoch vgCorrect) in
  ret vgCorrect rv'<rv
  where
  open StateTransProps

  rmPre  = peerStates pre pid
  rmPost = LBFT-post (handleProposal 0 pm) rmPre

  outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)

  esEpoch≡v'Epoch : Voting.VoteGeneratedCorrect rmPre rmPost v (pm ^∙ pmProposal) → peerStates pre pid ^∙ rmEpochState ∙ esEpoch ≡ v' ^∙ vEpoch
  esEpoch≡v'Epoch vgCorrect
    with invariantsCorrect pid pre preach
  esEpoch≡v'Epoch (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡ lv≡))) blockTriggered) | StateInvariants.mkRoundManagerInv rmCorrect blockTreeInv epochsMatch _ =
    -- TODO-3: This requires extending StateInvariants.RoundManagerInv` to track that the epoch of the last vote sent (if it exists) is the same as the peer's epoch as stored in safety data
    sym $ begin
      (v' ^∙ vEpoch)                   ≡⟨ sym eid≡ ⟩
      (v ^∙ vEpoch)                    ≡⟨ {!!} ⟩
      (rmPre ^∙ lSafetyData ∙ sdEpoch) ≡⟨ sym epochsMatch ⟩
      rmPre ^∙ rmEpochState ∙ esEpoch  ∎
    where
    open ≡-Reasoning
  esEpoch≡v'Epoch (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr< lvr≡))) blockTriggered) | StateInvariants.mkRoundManagerInv rmCorrect blockTreeInv epochsMatch _ =
    trans epochsMatch (trans sdEpoch≡? (trans (sym (proj₁ (Voting.VoteMadeFromBlock⇒VoteEpochRoundIs{v}{pm ^∙ pmProposal} blockTriggered))) eid≡))

  ret : Voting.VoteGeneratedCorrect (peerStates pre pid) _ v (pm ^∙ pmProposal) → _ → _
  ret (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡ lv≡))) blockTriggered) rv'<lvr
    with <-cmp (v' ^∙ vRound) (v ^∙ vRound)
  ... | tri< rv'<rv ¬rv'=rv ¬rv'>rv =
    inj₁ rv'<rv
  ... | tri≈ ¬rv'<rv rv'=rv ¬rv'>rv =
     ⊥-elim (¬msb (peerLastVoteSentB4 preach (trans lv≡v (sym lv≡)) hpk sig v'⊂m' m'∈pool (sym rv'=rv)))
  ... | tri> ¬rv'<rv ¬rv'=rv rv'>rv =
    -- TODO-2: prove `rmPre ^∙ lSafetyData ∙ sdLastVotedRound ≡ v ^∙ vRound` (waiting on: updates to `StateInvariants.RoundManagerInv`).
    -- We need to prove from `lv≡v` that the last voted round is same as the
    -- round of `v`, which requires tracking that the round of `sdLastVote` is
    -- the same as `sdLastVotedRound`
    ⊥-elim (≤⇒≯ (≤-trans rv'<lvr {!!}) rv'>rv)

  ret (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr< lvr≡))) blockTriggered) rv'<lvr =
    inj₁ (≤-trans (s≤s rv'<lvr) (≤-trans lvr< (≡⇒≤ (sym lvr≡))))
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , V x} m∈pool ini) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡ = {!!}
