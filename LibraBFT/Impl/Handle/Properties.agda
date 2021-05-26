{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module provides some scaffolding to define the handlers for our fake/simple "implementation"
-- and connect them to the interface of the SystemModel.

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Impl.Properties.Aux  -- TODO-1: maybe Aux properties should be in this file?
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

module LibraBFT.Impl.Handle.Properties where
  open import LibraBFT.Impl.Consensus.RoundManager
  open import LibraBFT.Impl.Handle

  ----- Properties that bridge the system model gap to the handler -----
  msgsToSendWereSent1 : ∀ {pid ts pm vm} {st : RoundManager}
                      → send (V vm) ∈ proj₂ (peerStep pid (P pm) ts st)
                      → ∃[ αs ] (SendVote vm αs ∈ LBFT-outs (handle pid (P pm) ts) st)
  msgsToSendWereSent1 {pid} {ts} {pm} {vm} {st} send∈acts
     with send∈acts
     -- The fake handler sends only to node 0 (fakeAuthor), so this doesn't
     -- need to be very general yet.
     -- TODO-1: generalize this proof so it will work when the set of recipients is
     -- not hard coded.

     -- The system model allows any message sent to be received by any peer (so the list of
     -- recipients it essentially ignored), meaning that our safety proofs will be for a slightly
     -- stronger model.  Progress proofs will require knowledge of recipients, though, so we will
     -- keep the implementation model faithful to the implementation.
  ...| here refl = fakeAuthor ∷ [] , here refl

  -- This captures which kinds of messages are sent by handling which kind of message.  It will
  -- require additional disjuncts when we implement processVote.
  msgsToSendWereSent : ∀ {pid nm m} {st : RoundManager}
                     → m ∈ proj₂ (peerStepWrapper pid nm st)
                     → send m ∈ proj₂ (peerStep pid nm 0 st)
                     × ∃[ vm ] ∃[ pm ] (m ≡ V vm × nm ≡ P pm)
  msgsToSendWereSent {pid} {nm = nm} {m} {st} m∈outs
    with nm
  ...| C _ = ⊥-elim (¬Any[] m∈outs)
  ...| V _ = ⊥-elim (¬Any[] m∈outs)
  ...| P pm
     with m∈outs
  ...| here v∈outs
       with m
  ...| P _ = ⊥-elim (P≢V v∈outs)
  ...| C _ = ⊥-elim (C≢V v∈outs)
  ...| V vm rewrite sym v∈outs = here refl , vm , pm , refl , refl

  proposalHandlerSentVote : ∀ {pid ts pm vm} {st : RoundManager}
                          → V vm ∈ proj₂ (peerStepWrapper pid (P pm) st)
                          → ∃[ αs ] (SendVote vm αs ∈ LBFT-outs (handle pid (P pm) ts) st)
  proposalHandlerSentVote {pid} {ts} {pm} {vm} {st} m∈outs
     with msgsToSendWereSent {pid} {P pm} {st = st} m∈outs
  ...| send∈ , vm , pm' , refl , refl
     with msgsToSendWereSent1 {pid} {ts} {pm'} {st = st} send∈
  ...| αs , sv = αs , sv

  ----- Properties that relate handler to system state -----

  data _∈RoundManager_ (qc : QuorumCert) (rm : RoundManager) : Set where
    inHQC : qc ≡ ₋rmHighestQC rm       → qc ∈RoundManager rm
    inHCC : qc ≡ ₋rmHighestCommitQC rm → qc ∈RoundManager rm

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
                 → ¬ (∈GenInfo (proj₂ vs))
                 → MsgWithSig∈ pk (proj₂ vs) (msgPool st)

   -- We can prove this easily because we don't yet do epoch changes,
   -- so only the initial EC is relevant.  Later, this will require us to use the fact that
   -- epoch changes require proof of committing an epoch-changing transaction.
  availEpochsConsistent :
     ∀{pid pid' v v' pk}{st : SystemState}
     → ReachableSystemState st
     → (pkvpf  : PeerCanSignForPK st v  pid  pk)
     → (pkvpf' : PeerCanSignForPK st v' pid' pk)
     → PeerCanSignForPK.𝓔 pkvpf ≡ PeerCanSignForPK.𝓔 pkvpf'
  availEpochsConsistent r (mkPCS4PK _ _ (inGenInfo refl) _ _ _)
                          (mkPCS4PK _ _ (inGenInfo refl) _ _ _) = refl

  -- Always true, so far, as no epoch changes.
  noEpochIdChangeYet : ∀ {pre : SystemState}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → (₋rmEC ppre) ^∙ rmEpoch ≡ (₋rmEC ppost) ^∙ rmEpoch
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
       → (V vm) ∈ outs
       → qc QC∈SyncInfo (vm ^∙ vmSyncInfo)
       → qc ∈RoundManager (peerStates pre pid)
  VoteMsgQCsFromRoundManager r (step-init _) _ _ ()
  VoteMsgQCsFromRoundManager {pid} {pre = pre} r (step-msg {_ , P pm} m∈pool pinit) {v} {vm}
                             hpk v⊂m m∈outs qc∈m
     with peerStates pre pid
  ...| rm
     with proposalHandlerSentVote {pid} {0} {pm} {vm} {rm} m∈outs
  ...| _ , v∈outs
     with qc∈m
  ...| withVoteSIHighQC refl
       = inHQC (cong ₋siHighestQuorumCert (procPMCerts≡ {0} {pm} {rm} v∈outs))

  VoteMsgQCsFromRoundManager {pid} {pre = pre} r (step-msg {_ , P pm} m∈pool pinit) {v} {vm1}
                             hpk v⊂m m∈outs qc∈m
     | rm
     | _ , v∈outs
     | withVoteSIHighCC hqcIsJust
     with cong ₋siHighestCommitCert (procPMCerts≡ {0} {pm} {rm} v∈outs)
  ...| refl
     with (rm ^∙ rmHighestQC) ≟QC (rm ^∙ rmHighestCommitQC)
  ...| true  because (ofʸ refl) = ⊥-elim (maybe-⊥ hqcIsJust refl)
  ...| false because _          = inHCC (just-injective (sym hqcIsJust))

  newVoteSameEpochGreaterRound : ∀ {pre : SystemState}{pid s' outs v m pk}
                               → ReachableSystemState pre
                               → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs)
                               → ¬ (∈GenInfo (₋vSignature v))
                               → Meta-Honest-PK pk
                               → v ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                               → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
                               → v ^∙ vEpoch ≡ (₋rmEC (peerStates pre pid)) ^∙ rmEpoch
                               × suc ((₋rmEC (peerStates pre pid)) ^∙ rmLastVotedRound) ≡ v ^∙ vRound  -- New vote for higher round than last voted
                               × v ^∙ vRound ≡ ((₋rmEC s') ^∙ rmLastVotedRound)     -- Last voted round is round of new vote
  newVoteSameEpochGreaterRound {pre = pre} {pid} {v = v} {m} {pk} r (step-msg {(_ , P pm)} msg∈pool pinit) ¬init hpk v⊂m m∈outs sig vnew
     rewrite pinit
     with msgsToSendWereSent {pid} {P pm} {m} {peerStates pre pid} m∈outs
  ...| _ , vm , _ , refl , refl
    with proposalHandlerSentVote {pid} {0} {pm} {vm} {peerStates pre pid} m∈outs
  ...| _ , v∈outs
     rewrite SendVote-inj-v  (Any-singleton⁻ v∈outs)
           | SendVote-inj-si (Any-singleton⁻ v∈outs)
    with v⊂m
       -- Rebuilding keeps the same signature, and the SyncInfo included with the
       -- VoteMsg sent comprises QCs from the peer's state.  Votes represented in
       -- those QCS have signatures that have been sent before, contradicting the
       -- assumption that v's signature has not been sent before.
  ...| vote∈vm {si} = refl , refl , refl
  ...| vote∈qc {vs = vs} {qc} vs∈qc v≈rbld (inV qc∈m)
                  rewrite cong ₋vSignature v≈rbld
                        | procPMCerts≡ {0} {pm} {peerStates pre pid} {vm} v∈outs
    with qcVotesSentB4 r pinit (VoteMsgQCsFromRoundManager r (step-msg msg∈pool pinit) hpk v⊂m (here refl) qc∈m) vs∈qc ¬init
  ...| sentb4 = ⊥-elim (vnew sentb4)

  -- We resist the temptation to combine this with the noEpochChangeYet because in future there will be epoch changes
  lastVoteRound-mono : ∀ {pre : SystemState}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → (₋rmEC ppre) ^∙ rmEpoch ≡ (₋rmEC ppost) ^∙ rmEpoch
                     → (₋rmEC ppre) ^∙ rmLastVotedRound ≤ (₋rmEC ppost) ^∙ rmLastVotedRound
  lastVoteRound-mono _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  lastVoteRound-mono _ ppre≡ (step-msg {(_ , m)} _ _) _
     with m
  ...| P p = const (≤-step (≤-reflexive refl))
  ...| V v = const (≤-reflexive refl)
  ...| C c = const (≤-reflexive refl)

