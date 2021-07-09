{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module provides some scaffolding to define the handlers for our fake/simple "implementation"
-- and connect them to the interface of the SystemModel.

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplFake.Consensus.RoundManager.Properties
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.ImplFake.Consensus.RoundManager
open import LibraBFT.ImplFake.Handle
open        ParamsWithInitAndHandlers FakeInitAndHandlers
open        PeerCanSignForPK

open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms FakeInitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

module LibraBFT.ImplFake.Handle.Properties where

  -- This proof is complete except for pieces that are directly about the handlers.  Our
  -- fake/simple handler does not yet obey the needed properties, so we can't finish this yet.
  impl-sps-avp : StepPeerState-AllValidParts
  -- In our fake/simple implementation, init and handling V and C msgs do not send any messages
  impl-sps-avp _ hpk (step-init _) m∈outs part⊂m ver         = ⊥-elim (¬Any[] m∈outs)
  impl-sps-avp _ hpk (step-msg {sndr , V vm} _ _) m∈outs _ _ = ⊥-elim (¬Any[] m∈outs)
  impl-sps-avp _ hpk (step-msg {sndr , C cm} _ _) m∈outs _ _ = ⊥-elim (¬Any[] m∈outs)
  -- These aren't true yet, because processProposalMsgM sends fake votes that don't follow the rules for ValidPartForPK
  impl-sps-avp preach hpk (step-msg {sndr , P pm} m∈pool ps≡) m∈outs v⊂m ver ¬init
     with m∈outs
     -- Handler sends at most one vote, so it can't be "there"
  ...| there {xs = xs} imp = ⊥-elim (¬Any[] imp)
  ...| here refl
     with v⊂m
  ...| vote∈qc vs∈qc rbld≈ qc∈m
     with qc∈m
  ...| xxx = {!x!}                -- We will prove that votes represented in the SyncInfo of a
                                  -- proposal message were sent before, so these will be inj₂.
                                  -- This will be based on an invariant of the implementation, for
                                  -- example that the QCs included in the SyncInfo of a VoteMsg have
                                  -- been sent before.  We will need to use hash injectivity and
                                  -- signature injectivity to ensure a different vote was not sent
                                  -- previously with the same signature.

  impl-sps-avp {pk = pk} {α = α} {st = st} preach hpk (step-msg {sndr , P pm} m∈pool ps≡) m∈outs v⊂m ver ¬init
     | here refl
     | vote∈vm {si}
     with MsgWithSig∈? {pk} {ver-signature ver} {msgPool st}
  ...| yes msg∈ = inj₂ msg∈
  ...| no  msg∉ = inj₁ ( mkPCS4PK {!!} (inGenInfo refl) {!!}
       -- The implementation will need to provide evidence that the peer is a member of
       -- the epoch of the message it's sending and that it is assigned pk for that epoch.
                        , msg∉)

  open Structural impl-sps-avp

  -- This captures which kinds of messages are sent by handling which kind of message.  It will
  -- require additional disjuncts when we implement processVote.
  msgsToSendWereSent : ∀ {pid nm m} {st : RoundManager}
                     → send m ∈ proj₂ (peerStep pid nm st)
                     → ∃[ vm ] ∃[ pm ] (m ≡ V vm × nm ≡ P pm)
  msgsToSendWereSent {pid} {nm = nm} {m} {st} m∈outs
    with nm
  ...| C _ = ⊥-elim (¬Any[] m∈outs)
  ...| V _ = ⊥-elim (¬Any[] m∈outs)
  ...| P pm
     with m∈outs
  ...| here v∈outs
       with m
  ...| P _ = ⊥-elim (P≢V (action-send-injective v∈outs))
  ...| C _ = ⊥-elim (C≢V (action-send-injective v∈outs))
  ...| V vm rewrite sym v∈outs = vm , pm , refl , refl

  ----- Properties that relate handler to system state -----

  data _∈RoundManager_ (qc : QuorumCert) (rm : RoundManager) : Set where
    inHQC : qc ≡ rm ^∙ rmHighestQC       → qc ∈RoundManager rm
    inHCC : qc ≡ rm ^∙ rmHighestCommitQC → qc ∈RoundManager rm

  postulate -- TODO-2: this will be proved for the implementation, confirming that honest
            -- participants only store QCs comprising votes that have actually been sent.
   -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
   -- Note that some implementations might not ensure this, but LibraBFT does
   -- because even the leader of the next round sends its own vote to itself,
   -- as opposed to using it to construct a QC using its own unsent vote.

   qcVotesSentB4 : ∀{pid qc vs pk}{st : SystemState}
                 → ReachableSystemState st
                 → initialised st pid ≡ initd
                 → qc ∈RoundManager (peerStates st pid)
                 → vs ∈ qcVotes qc
                 → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
                 → MsgWithSig∈ pk (proj₂ vs) (msgPool st)

  -- We can prove this easily because we don't yet do epoch changes,
  -- so only the initial EC is relevant.  Later, this will require us to use the fact that
  -- epoch changes require proof of committing an epoch-changing transaction.
  availEpochsConsistent :
     ∀{pid pid' v v' pk}{st : SystemState}
     → (pkvpf  : PeerCanSignForPK st v  pid  pk)
     → (pkvpf' : PeerCanSignForPK st v' pid' pk)
     → v ^∙ vEpoch ≡ v' ^∙ vEpoch
     → pcs4𝓔 pkvpf ≡ pcs4𝓔 pkvpf'
  availEpochsConsistent (mkPCS4PK _ (inGenInfo refl) _)
                        (mkPCS4PK _ (inGenInfo refl) _) refl = refl

  -- Always true, so far, as no epoch changes.
  noEpochIdChangeYet : ∀ {pre : SystemState}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → ppre ^∙ rmEpoch ≡ ppost ^∙ rmEpoch
  noEpochIdChangeYet _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  noEpochIdChangeYet _ ppre≡ (step-msg {(_ , m)} _ _) ini
     with m
  ...| P p = refl
  ...| V v = refl
  ...| C c = refl

  open SyncInfo

  -- QCs in VoteMsg come from RoundManager
  VoteMsgQCsFromRoundManager :
       ∀ {pid s' outs pk}{pre : SystemState}
       → ReachableSystemState pre
       -- For any honest call to /handle/ or /init/,
       → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
       → ∀{v vm qc} → Meta-Honest-PK pk
       -- For every vote v represented in a message output by the call
       → v ⊂Msg (V vm)
       → send (V vm) ∈ outs
       → qc QC∈SyncInfo (vm ^∙ vmSyncInfo)
       → qc ∈RoundManager (peerStates pre pid)
  VoteMsgQCsFromRoundManager r (step-init _) _ _ ()
  VoteMsgQCsFromRoundManager {pid} {pre = pre} r (step-msg {_ , P pm} m∈pool pinit) {v} {vm}
                             hpk v⊂m m∈outs qc∈m
     with peerStates pre pid
  ...| rm
     with m∈outs
  ...| here refl
     with qc∈m
  ...| withVoteSIHighQC refl
       = inHQC refl

  VoteMsgQCsFromRoundManager {pid} {pre = pre} r (step-msg {_ , P pm} m∈pool pinit) {v} {vm1}
                             hpk v⊂m m∈outs qc∈m
     | rm
     | here refl
     | withVoteSIHighCC hqcIsJust
     with (rm ^∙ rmHighestQC) ≟QC (rm ^∙ rmHighestCommitQC)
  ...| true  because (ofʸ refl) = ⊥-elim (maybe-⊥ hqcIsJust refl)
  ...| false because _          = inHCC (just-injective (sym hqcIsJust))

  newVoteSameEpochGreaterRound : ∀ {pre : SystemState}{pid s' outs v m pk}
                               → ReachableSystemState pre
                               → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs)
                               → ¬ (∈GenInfo-impl genesisInfo (_vSignature v))
                               → Meta-Honest-PK pk
                               → v ⊂Msg m → send m ∈ outs → (sig : WithVerSig pk v)
                               → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                               → v ^∙ vEpoch ≡ (peerStates pre pid) ^∙ rmEpoch
                               × v ^∙ vRound ≡ (s' ^∙ rmLastVotedRound)     -- Last voted round is round of new vote
  newVoteSameEpochGreaterRound {pre = pre} {pid} {v = v} {m} {pk} r (step-msg {(_ , P pm)} msg∈pool pinit) ¬init hpk v⊂m m∈outs sig vnew
     rewrite pinit
     with msgsToSendWereSent {pid} {P pm} {m} {peerStates pre pid} m∈outs
  ...| _ , vm , _ , refl
    with m∈outs
  ...| here refl
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈vm {si} = refl , refl
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong _vSignature v≈rbld
    with qcVotesSentB4 r pinit (VoteMsgQCsFromRoundManager r (step-msg msg∈pool pinit) hpk v⊂m (here refl) qc∈m) vs∈qc ¬init
  ...| sentb4 = ⊥-elim (vnew sentb4)

  -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
  lastVoteRound-mono : ∀ {pre : SystemState}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → ppre ^∙ rmEpoch ≡ ppost ^∙ rmEpoch
                     → ppre ^∙ rmLastVotedRound ≤ ppost ^∙ rmLastVotedRound
  lastVoteRound-mono _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  lastVoteRound-mono _ ppre≡ (step-msg {(_ , m)} _ _) _
     with m
  ...| P p = const (≤-step (≤-reflexive refl))
  ...| V v = const (≤-reflexive refl)
  ...| C c = const (≤-reflexive refl)

  postulate -- TODO-1: prove it

    ¬genVotesRound≢0  : ∀{pid s' outs pk}{pre : SystemState}
                      → ReachableSystemState pre
                      -- For any honest call to /handle/ or /init/,
                      → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
                      → ∀{v m} → Meta-Honest-PK pk
                      -- For signed every vote v of every outputted message
                      → v ⊂Msg m → send m ∈ outs
                      → (wvs : WithVerSig pk v)
                      → (¬ ∈GenInfo-impl genesisInfo (ver-signature wvs))
                      → v ^∙ vRound ≢ 0
