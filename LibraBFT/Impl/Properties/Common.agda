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
import      LibraBFT.Impl.Handle                       as Handle
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open Invariants
open RoundManagerTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers Handle.InitHandler.InitAndHandlers
open        PeerCanSignForPK

open import LibraBFT.ImplShared.Util.HashCollisions Handle.InitHandler.InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms
                               Handle.InitHandler.InitAndHandlers
                               PeerCanSignForPK PeerCanSignForPK-stable
import      LibraBFT.Impl.Handle.InitProperties as IP

-- This module contains definitions and lemmas used by proofs of the
-- implementation obligations for VotesOnce and PreferredRoundRule.

module LibraBFT.Impl.Properties.Common where

postulate -- TODO-3: prove (note: advanced; waiting on: `handle`)
  -- This will require updates to the existing proofs for the peer handlers. We
  -- will need to show that honest peers sign things only for their only PK, and
  -- that they either resend messages signed before or if sending a new one,
  -- that signature hasn't been sent before
  impl-sps-avp : StepPeerState-AllValidParts

open Structural impl-sps-avp

-- We can prove this easily for the Agda model because (unlike the Haskell
-- prototype) it does not yet do epoch changes, so only the initial EC is
-- relevant. Later, this will require us to use the fact that epoch changes
-- require proof of committing an epoch-changing transaction.
availEpochsConsistent :
   ∀{pid pid' v v' pk}{st : SystemState}
   → (pkvpf  : PeerCanSignForPK st v  pid  pk)
   → (pkvpf' : PeerCanSignForPK st v' pid' pk)
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → pcs4𝓔 pkvpf ≡ pcs4𝓔 pkvpf'
availEpochsConsistent (mkPCS4PK _ (inBootstrapInfo refl) _) (mkPCS4PK _ (inBootstrapInfo refl) _) refl = refl

postulate -- TODO-1: Prove (waiting on: complete definition of `initRM`)
  uninitQcs∈Bootstrap
    : ∀ {pid qc vs}{st : SystemState}
      → ReachableSystemState st
      → initialised st pid ≡ uninitd
      → qc QCProps.∈RoundManager (peerStates st pid)
      → vs ∈ qcVotes qc
      → ∈BootstrapInfo-impl fakeBootstrapInfo (proj₂ vs)

module ∈BootstrapInfoProps where
  sameSig∉ : ∀ {pk} {v v' : Vote}
             → (sig : WithVerSig pk v) (sig' : WithVerSig pk v')
             → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig)
             → ver-signature sig' ≡ ver-signature sig
             → ¬ ∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig')
  sameSig∉ _ _ ¬bootstrap ≡sig rewrite ≡sig = ¬bootstrap

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
  msb4 preach step (mkPCS4PK 𝓔@._ (inBootstrapInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)) hpk sig mws∈pool =
    mkPCS4PK 𝓔 (inBootstrapInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)

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
    → Meta-Honest-PK pk
    → (sig : WithVerSig pk v)
    → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig))
    → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
    → initialised st pid ≡ initd

  mws∈pool⇒initd{pk = pk}{v} (step-s{pre = pre} rss step@(step-peer sp@(step-cheat cmc))) pcsfpk hpk sig ¬bootstrap mws∈pool =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre) hpk sig ¬bootstrap mws∈poolPre)
    where
    ¬bootstrap' = ∈BootstrapInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬bootstrap (msgSameSig mws∈pool)

    mws∈poolPre : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre = ¬cheatForgeNew sp refl unit hpk mws∈pool ¬bootstrap'

  mws∈pool⇒initd{pid₁}{pk = pk} (step-s{pre = pre} rss step@(step-peer sp@(step-honest{pid₂} sps@(step-init {rm} handler-pid-bsi≡just-rm×acts uni)))) pcsfpk hpk sig ¬bootstrap mws∈pool
     with pid₁ ≟ pid₂
  ...| yes refl = StepPeer-post-lemma2 {pre = pre} sps
  ...| no neq
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬bootstrap' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬bootstrap' = ∈BootstrapInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬bootstrap (msgSameSig mws∈pool)
  ...| Right mws∈poolPre = peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬bootstrap mws∈poolPre')
     where
     mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
     mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre
  ...| Left (send∈acts , pks4pk₂ , ¬sentb4)
     with IP.initHandlerSpec.contract pid₂ fakeBootstrapInfo handler-pid-bsi≡just-rm×acts
  ...| IP-initHandlerSpec-ContractOk-pid-bsi-rm-acts
     with msg⊆ mws∈pool
  ...| vote∈vm
     = ⊥-elim (P≢V (sym (proj₁ (proj₂ (IP.initHandlerSpec.ContractOk.isInitPM
                                        IP-initHandlerSpec-ContractOk-pid-bsi-rm-acts send∈acts)))))
  ...| vote∈qc vs∈qc _ qc∈pm
     with IP.initHandlerSpec.ContractOk.isInitPM IP-initHandlerSpec-ContractOk-pid-bsi-rm-acts send∈acts
  ...| (pm , refl , noSigs) = ⊥-elim (noSigs qc∈pm vs∈qc)

  mws∈pool⇒initd{pid₁}{pk}{v} (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬bootstrap mws∈pool
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬bootstrap' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬bootstrap' = ∈BootstrapInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬bootstrap (msgSameSig mws∈pool)
  ... | Left (m∈outs , pcsfpk' , ¬msb4)
     with pid≡
     where
     vd₁≡vd₂ : v ≡L msgPart mws∈pool at vVoteData
     vd₁≡vd₂ = either (⊥-elim ∘ PerReachableState.meta-sha256-cr rss) id (sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool))

     pid≡ : pid₁ ≡ pid₂
     pid≡ = PeerCanSignForPKProps.pidInjective pcsfpk pcsfpk' (cong (_^∙ vdProposed ∙ biEpoch) vd₁≡vd₂)
  ... | refl rewrite StepPeer-post-lemma2{pid₂}{pre = pre} sps = refl

  mws∈pool⇒initd{pid₁}{pk}  (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬bootstrap mws∈pool | Right mws∈poolPre =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬bootstrap mws∈poolPre')
    where
    mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre

  mws∈pool⇒epoch≡
    : ∀ {pid v s' outs pk}{st : SystemState}
      → ReachableSystemState st
      → (sps : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → s' ^∙ rmEpoch ≡ v ^∙ vEpoch
      → peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch
  mws∈pool⇒epoch≡ rss (step-init _ uni) pcsfpk hpk sig ¬bootstrap mws∈pool epoch≡ =
    absurd (uninitd ≡ initd) case (trans (sym uni) ini) of λ ()
    where
    ini = mws∈pool⇒initd rss pcsfpk hpk sig ¬bootstrap mws∈pool
  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{_ , P pm} m∈pool ini) pcsfpk hpk sig ¬bootstrap mws∈pool epoch≡ = begin
    hpPre ^∙ rmEpoch ≡⟨ noEpochChange ⟩
    hpPos ^∙ rmEpoch ≡⟨ epoch≡ ⟩
    v ^∙ vEpoch      ∎
    where
    hpPool = msgPool st
    hpPre  = peerStates st pid
    hpPos  = LBFT-post (handleProposal 0 pm) hpPre

    open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre)
    open ≡-Reasoning

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , V vm} _ _) pcsfpk hpk sig ¬bootstrap mws∈pool epoch≡ = begin
    hvPre ^∙ rmEpoch ≡⟨ noEpochChange ⟩
    hvPos ^∙ rmEpoch ≡⟨ epoch≡ ⟩
    v ^∙ vEpoch      ∎
    where
    hvPre = peerStates st pid
    hvPos = LBFT-post (handleVote 0 vm) hvPre

    open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool st) hvPre)
    open ≡-Reasoning

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , C cm} _ _) pcsfpk hpk sig ¬bootstrap mws∈pool epoch≡ = epoch≡

