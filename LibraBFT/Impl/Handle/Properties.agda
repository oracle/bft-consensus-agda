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
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP concSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

module LibraBFT.Impl.Handle.Properties
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
  open import LibraBFT.Impl.Consensus.RoundManager hash hash-cr
  open import LibraBFT.Impl.Handle hash hash-cr

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

  msgsToSendWereSent : ∀ {pid ts nm m} {st : RoundManager}
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
                 → vm ^∙ vmSyncInfo ≡ SyncInfo∙new (ps ^∙ rmHighestQC) (ps ^∙ rmHighestCommitQC)
                 → vs ∈ qcVotes q
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
