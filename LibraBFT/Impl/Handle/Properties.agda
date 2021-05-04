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
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

open import LibraBFT.Impl.Properties.Aux  -- TODO-1: maybe Aux properties should be in this file?
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManagerAndMeta ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp
open import LibraBFT.Abstract.Util.AvailableEpochs NodeId ℓ-EC EpochConfig EpochConfig.epochId


module LibraBFT.Impl.Handle.Properties
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
  open import LibraBFT.Impl.Consensus.RoundManager hash hash-cr
  open import LibraBFT.Impl.Handle hash hash-cr

  ----- Properties that bridge the system model gap to the handler -----
  msgsToSendWereSent1 : ∀ {pid ts pm vm} {st : RoundManagerAndMeta}
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

  msgsToSendWereSent : ∀ {pid ts nm m} {st : RoundManagerAndMeta}
                     → m ∈ proj₂ (peerStepWrapper pid nm st)
                     → ∃[ vm ] (m ≡ V vm × send (V vm) ∈ proj₂ (peerStep pid nm ts st))
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
  ...| V vm rewrite sym v∈outs = vm , refl , here refl

  ----- Properties that relate handler to system state -----

  data PeerKnowsPCS4 (st : SystemState) (v : Vote) (pid : NodeId) (pk : PK) : Set ℓ-EC where
    inPre  : initialised st pid ≡ initd
           → PeerCanSignForPK (peerStates st pid) v pid pk
           → PeerKnowsPCS4 st v pid pk
    inPost : ∀ {s outs}
           → initialised st pid ≡ initd
           → StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s , outs)
           → PeerCanSignForPK s v pid pk
           → PeerKnowsPCS4 st v pid pk

  𝓔ofPeerKnowsPCS4 : ∀ {st v pid pk}
                  → PeerKnowsPCS4 st v pid pk
                  → EpochConfig
  𝓔ofPeerKnowsPCS4 (inPre  _ pcsf)   = PeerCanSignForPK.𝓔 pcsf
  𝓔ofPeerKnowsPCS4 (inPost _ _ pcsf) = PeerCanSignForPK.𝓔 pcsf

  PeerKnowsPCS4⇒EC≡ : ∀ {st v pid pk}
                    → ReachableSystemState st
                    →(pkpcs : PeerKnowsPCS4 st v pid pk)
                    → 𝓔ofPeerKnowsPCS4 pkpcs ≡ init-EC genInfo
  PeerKnowsPCS4⇒EC≡ step-0 (inPre  ini _  ) = ⊥-elim (uninitd≢initd ini)
  PeerKnowsPCS4⇒EC≡ step-0 (inPost ini _ _) = ⊥-elim (uninitd≢initd ini)
  -- Cheat step does not modify peer states or initialised

  -- This is tricky.  For inPost, the StepPeerState cannot be transferred back to the previous state
  -- because the cheat step changes the msgPool.  This suggests that we have the wrong notion of
  -- PeerCanSignForPK.  Why does a PeerState even have to record the EpochConfigs it knows about?  I
  -- am starting to think that PeerCanSignForPK should be a function of SystemState, not peerState.
  -- For example, for the first epoch, it is defined in terms of genInfo, and for subsequent epochs
  -- that result (in future) from epoch changes, we need to know that a change to an epoch that
  -- enables the peer to sign for the given PK has occurred.  Evidence of this can be a CommitMsg
  -- containing evidence of committing an EpochChanging transaction or it could be an
  -- EpochChangeProof message.  It is not clear to me that we need to track all the epoch configs in
  -- (meta) peerState.  What we need is to be able to prove StepPeerState-AllValidParts.  If
  -- PeerCanSignForPK is defined in terms of SystemState, then we can just provide evidence that
  -- there is an EpochConfig in the system state that says the peer's current epoch (the one for
  -- which it might send messages) allows it to sign for a PK in that epoch.  I think this approach
  -- will eliminate the PeerKnowsPCS4 business that I'm struggling with here.
  PeerKnowsPCS4⇒EC≡             (step-s r (step-peer        (step-cheat  x))) pkpcs = PeerKnowsPCS4⇒EC≡ r {!pkpcs!}
  PeerKnowsPCS4⇒EC≡ {pid = pid} (step-s r (step-peer {pid'} (step-honest (step-init uni)))) (inPre ini pcs)
     with pid ≟ pid'
  ...| no  neq  = {! ini !}
  ...| yes refl = ⊥-elim (uninitd≢initd (trans (sym uni) {!ini!})) -- (trans (sym (override-target-≡ {a = pid'}  )) {!ini!})))
  PeerKnowsPCS4⇒EC≡ (step-s r (step-peer (step-honest (step-init uni)))) (inPost ini _ _) = {!!}
  PeerKnowsPCS4⇒EC≡ (step-s r (step-peer (step-honest (step-msg x x₁)))) pkpcs = {!!}

  postulate -- TODO-2: this will be proved for the implementation, confirming that honest
            -- participants only store QCs comprising votes that have actually been sent.
   -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
   -- Note that some implementations might not ensure this, but LibraBFT does
   -- because even the leader of the next round sends its own vote to itself,
   -- as opposed to using it to construct a QC using its own unsent vote.
   qcVotesSentB4 : ∀{pid ps vs pk q vm}{st : SystemState}
                 → ReachableSystemState st
                 → initialised st pid ≡ initd
                 → ps ≡ peerStates st pid
                 → q QC∈VoteMsg vm
                 → vm ^∙ vmSyncInfo ≡ mkSyncInfo (₋rmamRM ps ^∙ rmHighestQC) (₋rmamRM ps ^∙ rmHighestCommitQC)
                 → vs ∈ qcVotes q
                 → MsgWithSig∈ pk (proj₂ vs) (msgPool st)

   -- We should be able to prove this easily now, because we don't yet do epoch changes,
   -- so only the initial EC is relevant.  Later, this will require us to use the fact that
   -- epoch changes require proof of committing an epoch-changing transaction (note that cheat
   -- steps do not modify meta data such as ₋epamMetaAvailepochs).
  availEpochsConsistent :
     ∀{pid pid' v v' pk}{st : SystemState}
     → ReachableSystemState st
     → (pkvpf  : PeerKnowsPCS4 st v  pid  pk)
     → (pkvpf' : PeerKnowsPCS4 st v' pid' pk)
     → 𝓔ofPeerKnowsPCS4 pkvpf ≡ 𝓔ofPeerKnowsPCS4 pkvpf'
  availEpochsConsistent r pkpcs pkpcs' = trans (PeerKnowsPCS4⇒EC≡ r pkpcs) (sym (PeerKnowsPCS4⇒EC≡ r pkpcs'))

  -- Always true, so far, as no epoch changes.
  noEpochIdChangeYet : ∀ {pre : SystemState}{pid}{ppre ppost msgs}
                     → ReachableSystemState pre
                     → ppre ≡ peerStates pre pid
                     → StepPeerState pid (msgPool pre) (initialised pre) ppre (ppost , msgs)
                     → initialised pre pid ≡ initd
                     → (₋rmamEC ppre) ^∙ rmEpoch ≡ (₋rmamEC ppost) ^∙ rmEpoch
  noEpochIdChangeYet _ ppre≡ (step-init uni) ini = ⊥-elim (uninitd≢initd (trans (sym uni) ini))
  noEpochIdChangeYet _ ppre≡ (step-msg {(_ , m)} _ _) ini
     with m
  ...| P p = refl
  ...| V v = refl
  ...| C c = refl

  postulate -- Not used yet, prove if needed
    eIdInRange : ∀{pid}{st : SystemState}
             → ReachableSystemState st
             → initialised st pid ≡ initd
             → ₋rmamEC (peerStates st pid) ^∙ rmEpoch < ₋rmamMetaNumEpochs (peerStates st pid)

