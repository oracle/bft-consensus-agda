{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Util.Types
open import Util.Prelude
import      Yasm.Base  as YB
import      Yasm.Types as YT

-- This module defines a model of a distributed system, parameterized by
-- SystemParameters, which establishes various application-dependent types,
-- handlers, etc.  The model supports a set of peers executing handlers in
-- response to messages received; these handlers can update the peer's
-- local state and/or send additional messages.  The model also enables
-- "cheat" steps, which can send arbitrary messages, except that they are
-- constrained to prevent a cheat step from introducing a new signature for
-- an "honest" public key.  The module also contains some structures for
-- proving properties of executions of the modeled system.

module Yasm.System
   (ℓ-PeerState : Level)
   (ℓ-VSFP      : Level)
   (parms      : YB.SystemTypeParameters ℓ-PeerState)
 where

 data InitStatus : Set where
   uninitd : InitStatus
   initd   : InitStatus
 open InitStatus

 uninitd≢initd : uninitd ≢ initd
 uninitd≢initd = λ ()

 open import Yasm.Base
 open SystemTypeParameters parms
 open import Util.FunctionOverride PeerId _≟PeerId_

 open import Util.PKCS

 SenderMsgPair : Set
 SenderMsgPair = PeerId × Msg

 actionToSMP : PeerId → YT.Action Msg → Maybe SenderMsgPair
 actionToSMP pid (YT.send m) = just (pid , m)

 SentMessages : Set
 SentMessages = List SenderMsgPair

 -- Convert the actions a peer `pid` took to a list of sent messages.
 -- Non-message actions are discarded.
 actionsToSentMessages : PeerId → List (YT.Action Msg) → SentMessages
 actionsToSentMessages pid = mapMaybe (actionToSMP pid)

 -- If the sender-message pair `(pid₁ , m)` is associated with the messages that
 -- were sent as a consequence of the actions `outs` of `pid₂`, then these two
 -- PIDs are equal and this peer performed a `send` action for that message.
 senderMsgPair∈⇒send∈ : ∀ {pid₁ pid₂ m} → (outs : List (YT.Action Msg)) →
       (pid₁ , m) ∈ (actionsToSentMessages pid₂ outs) →
       (YT.send m ∈ outs) × pid₁ ≡ pid₂
 senderMsgPair∈⇒send∈ (YT.send m ∷ outs) (here refl) = (here refl , refl)
 senderMsgPair∈⇒send∈ (YT.send m ∷ outs) (there pm∈)
    with senderMsgPair∈⇒send∈ outs pm∈
 ...| m∈outs , refl = (there m∈outs) , refl

 -- The model supports sending messages that contain some fields that are
 -- /not/ covered by the message's signature.  Therefore, given a message
 -- with a verifiable signature, it is possible for a propositionally
 -- different message that verifies against the same signature to have been
 -- sent before, which is captured by the following definition.
 record MsgWithSig∈ (pk : PK)(sig : Signature)(pool : SentMessages) : Set where
   constructor mkMsgWithSig∈
   field
     msgWhole   : Msg
     msgPart    : Part
     msg⊆       : msgPart ⊂MsgG msgWhole
     msgSender  : PeerId
     msg∈pool   : (msgSender , msgWhole) ∈ pool
     msgSigned  : WithVerSig pk msgPart
     msgSameSig : ver-signature msgSigned ≡ sig
 open MsgWithSig∈ public

 postulate  -- TODO-1: prove it
   MsgWithSig∈? : ∀ {pk} {sig} {pool} → Dec (MsgWithSig∈ pk sig pool)

 MsgWithSig∈-++ʳ : ∀{pk sig pool ms} → MsgWithSig∈ pk sig pool → MsgWithSig∈ pk sig (ms ++ pool)
 MsgWithSig∈-++ʳ {ms = pre} msig = record
    { msgWhole   = msgWhole msig
    ; msgPart    = msgPart  msig
    ; msg⊆       = msg⊆     msig
    ; msg∈pool   = Any-++ʳ pre (msg∈pool msig)
    ; msgSigned  = msgSigned msig
    ; msgSameSig = msgSameSig msig
    }

 MsgWithSig∈-++ˡ : ∀{pk sig pool ms} → MsgWithSig∈ pk sig ms → MsgWithSig∈ pk sig (ms ++ pool)
 MsgWithSig∈-++ˡ {ms = pre} msig = record
    { msgWhole   = msgWhole msig
    ; msgPart    = msgPart  msig
    ; msg⊆       = msg⊆     msig
    ; msg∈pool   = Any-++ˡ (msg∈pool msig)
    ; msgSigned  = msgSigned msig
    ; msgSameSig = msgSameSig msig
    }

 MsgWithSig∈-transp : ∀{pk sig pool pool'}
                    → (mws : MsgWithSig∈ pk sig pool)
                    → (msgSender mws , msgWhole mws) ∈ pool'
                    → MsgWithSig∈ pk sig pool'
 MsgWithSig∈-transp msig ∈pool' = record
    { msgWhole   = msgWhole msig
    ; msgPart    = msgPart  msig
    ; msg⊆       = msg⊆     msig
    ; msg∈pool   = ∈pool'
    ; msgSigned  = msgSigned msig
    ; msgSameSig = msgSameSig msig
    }

 -- * The System State
 --
 -- A system consists in a partial map from PeerId to PeerState, a pool
 -- of sent messages and a number of available epochs.
 record SystemState : Set (ℓ+1 ℓ-PeerState) where
   field
     peerStates  : PeerId → PeerState
     initialised : PeerId → InitStatus
     msgPool     : SentMessages          -- All messages ever sent
 open SystemState public

 module WithInitAndHandlers (iiah : SystemInitAndHandlers ℓ-PeerState parms) where
   open SystemInitAndHandlers iiah

   -- * Forbidding the Forging of Signatures
   --
   -- Whenever our reasoning must involve digital signatures, it is standard
   -- to talk about EUF-CMA resistant signature schemes. Informally, this captures
   -- signatures schemes that cannot be compromised by certain adversaries.
   -- Formally, it means that for any probabilistic-polynomial-time adversary 𝓐,
   -- and some security parameter k:
   --
   --      Pr[ EUF-CMA(k) ] ≤ ε(k) for ε a negigible function.
   --
   -- EUF-CMA is defined as:
   --
   -- EUF-CMA(k):                           |  O(m):
   --   L        ← ∅                        |    σ ← Sign(sk , m)
   --   (pk, sk) ← Gen(k)                   |    L ← L ∪ { m }
   --   (m , σ)  ← 𝓐ᴼ(pk)                   |    return σ
   --   return (Verify(pk, m, σ) ∧ m ∉ L)   |
   --
   -- This says that 𝓐 cannot create a message that has /not yet been signed/ and
   -- forge a signature for it. The list 'L' keeps track of the messages that 𝓐
   -- asked to be signed by the oracle.
   --
   -- Because the probability of the adversary to win the EUF-CMA(k) game
   -- approaches 0 as k increases; it is reasonable to assume that winning
   -- the game is /impossible/ for realistic security parameters.
   --
   -- EUF-CMA security is incorporated into our model by constraining messages
   -- sent by a cheat step to ensure that for every verifiably signed part of
   -- such a message, if there is a signature on the part, then it is either for
   -- a dishonest public key (in which cases it's secret key may have been leaked),
   -- or a message has been sent with the same signature before (in which case the
   -- signature is simply being "replayed" from a previous message).
   --
   -- Dishonest (or "cheat") messages are those that are not the result of
   -- a /handle/ or /init/ call, but rather are the result of a /cheat/ step.
   --
   -- A part of a cheat message can contain a verifiable signature only if it
   -- is for a dishonest public key, or a message with the same signature has
   -- been sent before or can be derived from BootstrapInfo (a cheater can
   -- "reuse" an honest signature sent before; it just can't produce a new
   -- one).  Note that this constraint precludes a peer sending a message
   -- that contains a new verifiable signature for an honest PK, even if the
   -- PK is the peer's own PK for some epoch (implying that the peer
   -- possesses the associated secret key).  In other words, a peer that is
   -- honest for a given epoch (by virtue of being a member of that epoch and
   -- being assigned an honest PK for the epoch), cannot send a message for
   -- that epoch using a cheat step.
   CheatPartConstraint : SentMessages → Part → Set
   CheatPartConstraint pool m = ∀{pk} → (ver : WithVerSig pk m)
                                      → ¬ ∈BootstrapInfo bootstrapInfo (ver-signature ver)
                                      → Meta-Dishonest-PK pk
                                      ⊎ MsgWithSig∈ pk (ver-signature ver) pool

   -- The only constraints on messages sent by cheat steps are that:
   -- * the sender is not an honest member in the epoch of any part of the message
   -- * the signature on any part of the message satisfies CheatCanSign, meaning
   --   that it is not a new signature for an honest public key
   CheatMsgConstraint : SentMessages → Msg → Set
   CheatMsgConstraint pool m = ∀{part} → part ⊂MsgG m → CheatPartConstraint pool part

   initialState : SystemState
   initialState = record
     { peerStates  = const initPS
     ; initialised = const uninitd
     ; msgPool     = []
     }

   -- * Small Step Semantics
   --
   -- The small step semantics are divided into three datatypes:
   --
   -- i)   StepPeerState executes a step through init or handle
   -- ii)  StepPeer executes a step through StepPeerState or cheat
   -- iii) Step transitions the system state by a StepPeer or by
   --      bringing a new epoch into existence

   -- The pre and post states of Honest peers are related iff
   data StepPeerState (pid : PeerId)(pool : SentMessages)
                      (peerInits : PeerId → InitStatus) (ps : PeerState) :
                      (PeerState × List (YT.Action Msg)) → Set ℓ-PeerState where
     -- An uninitialized peer can be initialized.  Note that initialiation step requires that the
     -- bootstrap function returns a just (i.e., initialisation succeeds).  In future, it may make
     -- sense to also model unsuccessful initialisation steps, which in principle could send
     -- messages or log output, etc.  In that case, the type of bootstrap would change (see comment
     -- at its definition)
     step-init : ∀ {st' acts}
               → bootstrap pid bootstrapInfo ≡ just (st' , acts)
               → peerInits pid ≡ uninitd
               → StepPeerState pid pool peerInits ps (st' , acts)

     -- The peer processes a message in the pool
     step-msg  : ∀{m}
               → m ∈ pool
               → peerInits pid ≡ initd
               → StepPeerState pid pool peerInits ps (handle pid (proj₂ m) ps)

   -- The pre-state of the suplied PeerId is related to the post-state and list of output messages iff:
   data StepPeer (pre : SystemState) : PeerId → PeerState → List (YT.Action Msg) → Set ℓ-PeerState where
     -- it can be obtained by a handle or init call.
     step-honest : ∀{pid st outs}
                 → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (st , outs)
                 → StepPeer pre pid st outs

     -- or the peer decides to cheat.  CheatMsgConstraint ensures it cannot
     -- forge signatures by honest peers.  Cheat steps do not modify peer
     -- state: these are maintained exclusively by the implementation
     -- handlers.
     step-cheat  : ∀{pid m}
                 → CheatMsgConstraint (msgPool pre) m
                 → StepPeer pre pid (peerStates pre pid) (YT.send m ∷ [])

   isCheat : ∀ {pre pid ms outs} → StepPeer pre pid ms outs → Set
   isCheat (step-honest _) = ⊥
   isCheat (step-cheat  _) = Unit

   initStatus : ∀ {pid pre ms outs}
              → StepPeer pre pid ms outs
              → InitStatus
              → InitStatus
   initStatus {pid} (step-honest _) preinit = initd
   initStatus {pid} (step-cheat  _) preinit = preinit

   -- Computes the post-sysstate for a given step-peer.
   StepPeer-post : ∀{pid st' outs}{pre : SystemState }
                 → StepPeer pre pid st' outs
                 → SystemState
   StepPeer-post {pid} {st'} {outs} {pre} sp = record pre
     { peerStates  = ⟦ peerStates pre  , pid ← st' ⟧
     ; initialised = ⟦ initialised pre , pid ← initStatus sp (initialised pre pid) ⟧
     ; msgPool     = actionsToSentMessages pid outs ++ msgPool pre
     }

   StepPeer-post-lemma : ∀{pid st' outs}{pre : SystemState}
                 → (pstep : StepPeer pre pid st' outs)
                 → st' ≡ peerStates (StepPeer-post pstep) pid
   StepPeer-post-lemma pstep = sym override-target-≡

   StepPeer-post-lemma2 : ∀{pid}{pre : SystemState}{st outs}
                        → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (st , outs))
                        → initialised (StepPeer-post {pid} {st} {outs} {pre} (step-honest sps)) pid ≡ initd
   StepPeer-post-lemma2 {pre = pre} _ = override-target-≡

   cheatStepDNMPeerStates : ∀{pid st' outs}{pre : SystemState}
                          → (theStep : StepPeer pre pid st' outs)
                          → isCheat theStep
                          → peerStates (StepPeer-post theStep) ≡ peerStates pre
   cheatStepDNMPeerStates {pid = pid} {pre = pre} (step-cheat _) _ = overrideSameVal-correct-ext {f = peerStates pre} {pid}

   cheatStepDNMInitialised : ∀{pid st' outs}{pre : SystemState}
                          → (theStep : StepPeer pre pid st' outs)
                          → isCheat theStep
                          → initialised (StepPeer-post theStep) ≡ initialised pre
   cheatStepDNMInitialised {pid = pid} {pre = pre} (step-cheat _) _ = overrideSameVal-correct-ext

   cheatStepDNMInitialised₁ : ∀{pid pid' st' outs}{pre : SystemState}
                          → (theStep : StepPeer pre pid st' outs)
                          → isCheat theStep
                          → initialised (StepPeer-post theStep) pid' ≡ initialised pre pid'
   cheatStepDNMInitialised₁ {pid} {pid'} {pre = pre} (step-cheat _) _ = overrideSameVal-correct pid pid'

   cheatStepDNMPeerStates₁ : ∀{pid pid' st' outs}{pre : SystemState}
                           → (theStep : StepPeer pre pid st' outs)
                           → isCheat theStep
                           → peerStates (StepPeer-post theStep) pid' ≡ peerStates pre pid'
   cheatStepDNMPeerStates₁ {pid} {pid'} (step-cheat _) x = overrideSameVal-correct pid pid'

   pids≢StepDNMPeerStates :  ∀{pid pid' s' outs}{pre : SystemState}
                           → (sps : StepPeerState pid' (msgPool pre) (initialised pre) (peerStates pre pid') (s' , outs))
                           → pid ≢ pid'
                           → peerStates pre pid ≡ peerStates (StepPeer-post {pid'} {s'} {outs} {pre} (step-honest sps)) pid
   pids≢StepDNMPeerStates sps pids≢ = override-target-≢ pids≢

   pids≢StepDNMInitialised : ∀ {pid pid' s' outs}{pre : SystemState}
                           → (sps : StepPeerState pid' (msgPool pre) (initialised pre) (peerStates pre pid') (s' , outs))
                           → pid ≢ pid'
                           → initialised pre pid ≡ initialised (StepPeer-post {pid'} {s'} {outs} {pre} (step-honest sps)) pid
   pids≢StepDNMInitialised sps pids≢ = override-target-≢ pids≢

   data Step : SystemState → SystemState → Set (ℓ+1 ℓ-PeerState) where
     -- TO-NOT-DO: it is tempting to merge this and StepPeer, now that step-peer
     -- is the only constructor here.  I started to do so, but it propagates many
     -- changes throughout the repo, and it's possible we will in future add steps
     -- not performed by a specific peer (for example, if we model some notion of
     -- time to prove liveness properties).
     step-peer : ∀{pid st' outs}{pre : SystemState}
               → (pstep : StepPeer pre pid st' outs)
               → Step pre (StepPeer-post pstep)


   msgs-stable : ∀ {pre : SystemState} {post : SystemState} {m}
               → (theStep : Step pre post)
               → m ∈ msgPool pre
               → m ∈ msgPool post
   msgs-stable (step-peer {pid = pid} {outs = outs} _) m∈ = Any-++ʳ (actionsToSentMessages pid outs) m∈

   peersRemainInitialized : ∀ {pid} {pre : SystemState} {post : SystemState}
                          → Step pre post
                          → initialised pre pid ≡ initd
                          → initialised post pid ≡ initd
   peersRemainInitialized {pid} (step-peer {pid'} step) isInitd
     with pid' ≟PeerId pid
   ...| no neq = isInitd
   ...| yes refl
     with step
   ... | step-honest {pidS} {st} {outs} stp = refl
   ... | step-cheat _ = isInitd

   peersRemainInitialized' : ∀ {pid} {pre : SystemState} {post : SystemState}
                           → Step pre post
                           → initialised post pid ≡ uninitd
                           → initialised pre  pid ≡ uninitd
   peersRemainInitialized' {pid} {pre} theStep@(step-peer {pid'} step) isUninitd
     with pid' ≟PeerId pid
   ...| no neq = isUninitd
   ...| yes refl
     with step
   ... | step-cheat _ = isUninitd
   ... | step-honest {pidS} {st} {outs} stp
     with (initialised pre pid)
   ... | uninitd = refl
   ... |   initd = absurd initd ≡ uninitd case  isUninitd of λ ()

   -- not used yet, but some proofs could probably be cleaned up using this,
   -- e.g., prevVoteRnd≤-pred-step in Impl.VotesOnce
   sendMessages-target : ∀ {m : SenderMsgPair} {sm : SentMessages} {ml : List SenderMsgPair}
                       → ¬ (m ∈ sm)
                       → m ∈ (ml ++ sm)
                       → m ∈ ml
   sendMessages-target {ml = ml} ¬m∈sm m∈++
     with Any-++⁻ ml m∈++
   ...| inj₁ m∈ml = m∈ml
   ...| inj₂ m∈sm = ⊥-elim (¬m∈sm m∈sm)

   -- * Reflexive-Transitive Closure

   data Step* : SystemState → SystemState → Set (ℓ+1 ℓ-PeerState) where
     step-0 : ∀{pre : SystemState}
            → Step* pre pre

     step-s : ∀{fst : SystemState}{pre : SystemState}{post : SystemState}
            → Step* fst pre
            → Step pre post
            → Step* fst post

   ReachableSystemState : SystemState → Set (ℓ+1 ℓ-PeerState)
   ReachableSystemState = Step* initialState

   peerStatePostSt : ∀ {pid s' s outs} {st : SystemState}
                   → (r : ReachableSystemState st)
                   → (stP : StepPeerState pid (msgPool st) (initialised st)
                                          (peerStates st pid) (s' , outs))
                   → peerStates (StepPeer-post {pre = st} (step-honest stP)) pid ≡ s
                   → s ≡ s'
   peerStatePostSt _ _ ps≡s = trans (sym ps≡s) override-target-≡

   Step*-trans : ∀ {st st' st''}
               → Step* st st'
               → Step* st' st''
               → Step* st st''
   Step*-trans r step-0 = r
   Step*-trans r (step-s tr x) = step-s (Step*-trans r tr) x

   Step*-initdStable : ∀{st st' pid}
                     → Step* st st'
                     → initialised st  pid ≡ initd
                     → initialised st' pid ≡ initd
   Step*-initdStable step-0 ini = ini
   Step*-initdStable {st} {pid = pid} (step-s {pre = pre} tr theStep) ini =
                     peersRemainInitialized theStep (Step*-initdStable tr ini)

   peerUninitState
     : ∀ {pid} {st₁ st₂ : SystemState}
       → Step* st₁ st₂
       → initialised st₂ pid ≡ uninitd
       → peerStates  st₂ pid ≡ peerStates st₁ pid
   peerUninitState step-0 uni = refl
   peerUninitState (step-s step* (step-peer sp@(step-cheat _))) uni =
     trans (cheatStepDNMPeerStates₁ sp unit)
       (peerUninitState step* (trans (sym $ cheatStepDNMInitialised₁ sp unit) uni))
   peerUninitState{pid} (step-s step* step@(step-peer{pre = pre} sp@(step-honest{pid'} sps))) uni
     with pid ≟PeerId pid'
   ... | no  pid≢ =
     trans (sym $ pids≢StepDNMPeerStates sps pid≢)
       (peerUninitState step* (trans (pids≢StepDNMInitialised{pre = pre} sps pid≢) uni))
   ... | yes pid≡ = case (initd ≡ uninitd ∋ absurd) of λ ()
     where
     absurd : initd ≡ uninitd
     absurd = begin
       initd                                          ≡⟨ sym $ StepPeer-post-lemma2{pre = pre} sps ⟩
       initialised (StepPeer-post{pre = pre} sp) pid' ≡⟨ cong (override (initialised pre) pid' initd) (sym pid≡) ⟩
       override (initialised pre) pid' initd pid      ≡⟨ uni ⟩
       uninitd                                        ∎
       where open ≡-Reasoning

   MsgWithSig∈-Step* : ∀{sig pk}{st : SystemState}{st' : SystemState}
                     → Step* st st'
                     → MsgWithSig∈ pk sig (msgPool st)
                     → MsgWithSig∈ pk sig (msgPool st')
   MsgWithSig∈-Step* step-0        msig = msig
   MsgWithSig∈-Step* (step-s tr (step-peer ps)) msig
     = MsgWithSig∈-++ʳ (MsgWithSig∈-Step* tr msig)

   MsgWithSig∈-Step*-part : ∀{sig pk}{st : SystemState}{st' : SystemState}
                          → (tr   : Step* st st')
                          → (msig : MsgWithSig∈ pk sig (msgPool st))
                          → msgPart msig ≡ msgPart (MsgWithSig∈-Step* tr msig)
   MsgWithSig∈-Step*-part step-0        msig = refl
   MsgWithSig∈-Step*-part (step-s tr (step-peer ps)) msig
     = MsgWithSig∈-Step*-part tr msig

   MsgWithSig∈-Step*-sender : ∀{sig pk}{st : SystemState}{st' : SystemState}
                            → (tr   : Step* st st')
                            → (msig : MsgWithSig∈ pk sig (msgPool st))
                            → msgSender msig ≡ msgSender (MsgWithSig∈-Step* tr msig)
   MsgWithSig∈-Step*-sender step-0        msig = refl
   MsgWithSig∈-Step*-sender (step-s tr (step-peer ps)) msig
     = MsgWithSig∈-Step*-sender tr msig

   ------------------------------------------

   -- Type synonym to express a relation over system states;
   SystemStateRel : ∀ {ℓ} → (SystemState → SystemState → Set (ℓ+1 ℓ-PeerState)) → Set (ℓ+1 (ℓ ℓ⊔ ℓ-PeerState))
   SystemStateRel {ℓ} P = ∀{st : SystemState}{st' : SystemState} → P st st' → Set (ℓ ℓ⊔ ℓ-PeerState)

   -- Just like Data.List.Any maps a predicate over elements to a predicate over lists,
   -- Any-step maps a relation over steps to a relation over steps in a trace.
   data Any-Step {ℓ : Level} (P : SystemStateRel {ℓ} Step) : SystemStateRel {ℓ} Step* where
    step-here  : ∀{fst : SystemState}{pre : SystemState}{post : SystemState}
               → (cont : Step* fst pre)
               → {this : Step pre post}(prf  : P this)
               → Any-Step P (step-s cont this)

    step-there : ∀{fst : SystemState}{pre : SystemState}{post : SystemState}
               → {cont : Step* fst pre}
               → {this : Step pre post}
               → (prf  : Any-Step {ℓ} P cont)
               → Any-Step P (step-s cont this)

   Any-Step-map : ∀ {ℓ}{P P' : SystemStateRel {ℓ} Step}
                → (∀ {pre : SystemState}{post : SystemState} → (x : Step pre post) → P x → P' x)
                → ∀ {fst lst} {tr : Step* fst lst}
                → Any-Step {ℓ} P tr
                → Any-Step {ℓ} P' tr
   Any-Step-map p⇒p' (step-here cont {this} prf) = step-here cont (p⇒p' this prf)
   Any-Step-map p⇒p' (step-there anyStep) = step-there (Any-Step-map p⇒p' anyStep)

   Any-Step-elim
     : ∀{ℓ}{ℓ-Q}{st₀ : SystemState}{st₁ : SystemState}{P : SystemStateRel {ℓ} Step}{Q : Set ℓ-Q}
     → {r : Step* st₀ st₁}
     → (P⇒Q : ∀{s : SystemState}{s' : SystemState}{st : Step s s'}
            → P st → Step* s' st₁ → Q)
     → Any-Step {ℓ} P r → Q
   Any-Step-elim P⇒Q (step-here cont prf)
     = P⇒Q prf step-0
   Any-Step-elim P⇒Q (step-there {this = this} f)
     = Any-Step-elim (λ p s → P⇒Q p (step-s s this)) f

   -- A predicate over peer states, parts and peerIds, representing which peers can send new
   -- signatures for which PKs.  The PeerState is needed to provide access to information the peer has
   -- about who uses what keys for what parts (in our case, EpochConfigs either derived from bootstrap
   -- information or agreed during epoch changes).
   ValidSenderForPK-type : Set (ℓ+1 ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
   ValidSenderForPK-type = SystemState → Part → PeerId → PK → Set ℓ-VSFP

   ValidSenderForPK-stable-type : ValidSenderForPK-type → Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
   ValidSenderForPK-stable-type vs4pk = ∀ {pre post part pid pk}
                                        → ReachableSystemState pre
                                        → Step pre post
                                        → vs4pk pre  part pid pk
                                        → vs4pk post part pid pk

   ------------------------------------------

   module _ (P : SystemState → Set) where

     Step*-Step-fold : (∀{pid st' outs}{st : SystemState}
                          → ReachableSystemState st
                          → (pstep : StepPeer st pid st' outs)
                          → P st
                          → P (StepPeer-post pstep))
                     → P initialState
                     → ∀{st : SystemState}
                     → (tr : ReachableSystemState st) → P st
     Step*-Step-fold fs p₀ step-0 = p₀
     Step*-Step-fold fs p₀ (step-s tr (step-peer p)) = fs tr p (Step*-Step-fold fs p₀ tr)
