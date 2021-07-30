{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

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

open StateInvariants
open StateTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module contains definitions and lemmas used by proofs of the
-- implementation obligations for VotesOnce and PreferredRoundRule.

module LibraBFT.Impl.Properties.Common where

postulate -- TODO-2: prove (waiting on: `handle`, refinements to handler contracts)
  -- This will be proved for the implementation, confirming that honest
  -- participants only store QCs comprising votes that have actually been sent.
  -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
  -- Note that some implementations might not ensure this, but LibraBFT does
  -- because even the leader of the next round sends its own vote to itself,
  -- as opposed to using it to construct a QC using its own unsent vote.
  qcVoteSigsSentB4
    : ∀ {pid qc vs pk}{st : SystemState}
      → ReachableSystemState st
      → initialised st pid ≡ initd
      → qc QC.∈RoundManager (peerStates st pid)
      → vs ∈ qcVotes qc
      → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
      → MsgWithSig∈ pk (proj₂ vs) (msgPool st)

module ∈GenInfoProps where
  sameSig∉ : ∀ {pk} {v v' : Vote}
             → (sig : WithVerSig pk v) (sig' : WithVerSig pk v')
             → ¬ ∈GenInfo-impl genesisInfo (ver-signature sig)
             → ver-signature sig' ≡ ver-signature sig
             → ¬ ∈GenInfo-impl genesisInfo (ver-signature sig')
  sameSig∉ _ _ ¬gen ≡sig rewrite ≡sig = ¬gen

-- Lemmas for `PeerCanSignForPK`
module PeerCanSignForPKProps where
  msb4 -- NOTE: This proof requires updating when we model epoch changes.
    : ∀ {pid v pk}{pre post : SystemState}
      → ReachableSystemState pre
      → Step pre post
      → PeerCanSignForPK post v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk
  msb4 preach step (mkPCS4PK 𝓔@._ (inGenInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)) hpk sig mws∈pool =
    mkPCS4PK 𝓔 (inGenInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)

  msb4-eid≡
    : ∀ {pre post : SystemState} {v v' pid pk}
      → ReachableSystemState pre
      → Step pre post
      → Meta-Honest-PK pk
      → PeerCanSignForPK post v pid pk
      → v ≡L v' at vEpoch
      → (sig' : WithVerSig pk v')
      → MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
      → PeerCanSignForPK pre v pid pk
  msb4-eid≡ rss step hpk pcsfpk ≡eid sig' mws' =
    peerCanSignEp≡ (msb4 rss step (peerCanSignEp≡ pcsfpk ≡eid) hpk sig' mws') (sym ≡eid)

  pidInjective
    : ∀ {pid pid' pk v v'}{st : SystemState}
      → PeerCanSignForPK st v  pid  pk
      → PeerCanSignForPK st v' pid' pk
      → v ^∙ vEpoch ≡ v' ^∙ vEpoch
      → pid ≡ pid'
  pidInjective{pid}{pid'}{pk} pcsfpk₁ pcsfpk₂ ≡epoch = begin
    pid         ≡⟨ sym (nid≡ (pcs4in𝓔 pcsfpk₁)) ⟩
    pcsfpk₁∙pid ≡⟨ PK-inj-same-ECs{pcs4𝓔 pcsfpk₁}{pcs4𝓔 pcsfpk₂}
                     (availEpochsConsistent pcsfpk₁ pcsfpk₂ ≡epoch) pcsfpk∙pk≡ ⟩
    pcsfpk₂∙pid ≡⟨ nid≡ (pcs4in𝓔 pcsfpk₂) ⟩
    pid'        ∎
    where
    open ≡-Reasoning
    open PeerCanSignForPKinEpoch
    open PeerCanSignForPK

    pcsfpk₁∙pid  = EpochConfig.toNodeId  (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁))
    pcsfpk₂∙pid  = EpochConfig.toNodeId  (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂))
    pcsfpk₁∙pk   = EpochConfig.getPubKey (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁))
    pcsfpk₂∙pk   = EpochConfig.getPubKey (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂))

    pcsfpk∙pk≡ : pcsfpk₁∙pk ≡ pcsfpk₂∙pk
    pcsfpk∙pk≡ = begin
      pcsfpk₁∙pk ≡⟨ pk≡ (pcs4in𝓔 pcsfpk₁) ⟩
      pk         ≡⟨ sym (pk≡ (pcs4in𝓔 pcsfpk₂)) ⟩
      pcsfpk₂∙pk ∎

module ReachableSystemStateProps where

  mws∈pool⇒initd
    : ∀ {pid pk v}{st : SystemState}
      → ReachableSystemState st
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → initialised st pid ≡ initd
  mws∈pool⇒initd{pk = pk}{v} (step-s{pre = pre} rss step@(step-peer sp@(step-cheat cmc))) pcsfpk hpk sig ¬gen mws∈pool =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre) hpk sig ¬gen mws∈poolPre)
    where
    ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)

    mws∈poolPre : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre = ¬cheatForgeNew sp refl unit hpk mws∈pool ¬gen'
  mws∈pool⇒initd{pid₁}{pk = pk} (step-s{pre = pre} rss step@(step-peer sp@(step-honest{pid₂} sps@(step-init ini)))) pcsfpk hpk sig ¬gen mws∈pool
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬gen' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)
  ... | Right mws∈poolPre = peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬gen mws∈poolPre')
    where
    mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre
  mws∈pool⇒initd{pid₁}{pk}{v} (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬gen mws∈pool
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬gen' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)
  ... | Left (m∈outs , pcsfpk' , ¬msb4)
     with pid≡
     where
     vd₁≡vd₂ : v ≡L msgPart mws∈pool at vVoteData
     vd₁≡vd₂ = either (⊥-elim ∘ PerReachableState.meta-sha256-cr rss) id (sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool))

     pid≡ : pid₁ ≡ pid₂
     pid≡ = PeerCanSignForPKProps.pidInjective pcsfpk pcsfpk' (cong (_^∙ vdProposed ∙ biEpoch) vd₁≡vd₂)
  ... | refl rewrite StepPeer-post-lemma2{pid₂}{pre = pre} sps = refl
  mws∈pool⇒initd{pid₁}{pk}  (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬gen mws∈pool | Right mws∈poolPre =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬gen mws∈poolPre')
    where
    mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre

  mws∈pool⇒epoch≡
    : ∀ {pid v s' outs pk}{st : SystemState}
      → ReachableSystemState st
      → (sps : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → s' ^∙ rmEpoch ≡ v ^∙ vEpoch
      → peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch
  mws∈pool⇒epoch≡ rss (step-init uni) pcsfpk hpk sig ¬gen mws∈pool epoch≡ =
    case uninitd ≡ initd ∋ trans (sym uni) ini of λ ()
    where
    ini = mws∈pool⇒initd rss pcsfpk hpk sig ¬gen mws∈pool
  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , P pm} _ _) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = begin
    hpPre ^∙ rmEpoch ≡⟨ noEpochChange ⟩
    hpPos ^∙ rmEpoch ≡⟨ epoch≡ ⟩
    v ^∙ vEpoch      ∎
    where
    hpPre = peerStates st pid
    hpPos = LBFT-post (handleProposal 0 pm) hpPre
    open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPre)
    open ≡-Reasoning

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , V vm} _ _) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = TODO
    where
    postulate -- TODO-3: prove (waiting on: epoch config changes)
      TODO : peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , C cm} _ _) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = TODO
    where
    postulate -- TODO-3: prove (waiting on: epoch config changes)
      TODO : peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch