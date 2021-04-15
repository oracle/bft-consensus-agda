{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
import      LibraBFT.Yasm.Base as LYB

-- This module defines a model of a distributed system, parameterized by
-- SystemParameters, which establishes various application-dependent types,
-- handlers, etc.  The model supports a set of peers executing handlers in
-- response to messages received; these handlers can update the peer's
-- local state and/or send additional messages.  The model also enables
-- "cheat" steps, which can send arbitrary messages, except that they are
-- constrained to prevent a cheat step from introducing a new signature for
-- an "honest" public key.  The module also contains some structures for
-- proving properties of executions of the modeled system.

module LibraBFT.Yasm.System
   (ℓ-PeerState : Level)
   (ℓ-VSFP      : Level)
   (parms      : LYB.SystemParameters ℓ-PeerState)
 where

 data InitStatus : Set where
   uninitd : InitStatus
   initd   : InitStatus
 open InitStatus

 uninitd≢initd : uninitd ≢ initd
 uninitd≢initd = λ ()

 open import LibraBFT.Yasm.Base
 open SystemParameters parms
 open import Util.FunctionOverride PeerId _≟PeerId_

 open import LibraBFT.Base.PKCS

 SenderMsgPair : Set
 SenderMsgPair = PeerId × Msg

 SentMessages : Set
 SentMessages = List SenderMsgPair

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
     msg⊆       : msgPart ⊂Msg msgWhole
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
 -- been sent before (a cheater can "reuse" an honest signature sent
 -- before; it just can't produce a new one).  Note that this constraint
 -- precludes a peer sending a message that contains a new verifiable
 -- signature for an honest PK, even if the PK is the peer's own PK for
 -- some epoch (implying that the peer possesses the associated secret
 -- key).  In other words, a peer that is honest for a given epoch (by
 -- virtue of being a member of that epoch and being assigned an honest PK
 -- for the epoch), cannot send a message for that epoch using a cheat
 -- step.
 CheatPartConstraint : SentMessages → Part → Set
 CheatPartConstraint pool m = ∀{pk} → (ver : WithVerSig pk m)
                                    → Meta-Dishonest-PK pk
                                    ⊎ MsgWithSig∈ pk (ver-signature ver) pool

 -- The only constraints on messages sent by cheat steps are that:
 -- * the sender is not an honest member in the epoch of any part of the message
 -- * the signature on any part of the message satisfies CheatCanSign, meaning
 --   that it is not a new signature for an honest public key
 CheatMsgConstraint : SentMessages → Msg → Set
 CheatMsgConstraint pool m = ∀{part} → part ⊂Msg m → CheatPartConstraint pool part

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
                    (PeerId → InitStatus) → (PeerState × List Msg) → Set where
   -- An uninitialized peer can be initialized
   step-init : peerInits pid ≡ uninitd
             → StepPeerState pid pool peerInits ps ⟦ peerInits , pid ← initd ⟧ (init pid genInfo)

   -- The peer processes a message in the pool
   step-msg  : ∀{m}
             → m ∈ pool
             → peerInits pid ≡ initd
             → StepPeerState pid pool peerInits ps peerInits (handle pid (proj₂ m) ps)

 -- The pre-state of the suplied PeerId is related to the post-state and list of output messages iff:
 data StepPeer (pre : SystemState) : PeerId → PeerState → List Msg → Set ℓ-PeerState where
   -- it can be obtained by a handle or init call.
   step-honest : ∀{pid st outs init'}
               → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) init' (st , outs)
               → StepPeer pre pid st outs

   -- or the peer decides to cheat.  CheatMsgConstraint ensures it cannot
   -- forge signatures by honest peers.  Cheat steps do not modify peer
   -- state: these are maintained exclusively by the implementation
   -- handlers.
   step-cheat  : ∀{pid}
               → (fm : SentMessages → PeerState → Msg)
               → let m = fm (msgPool pre) (peerStates pre pid)
                  in CheatMsgConstraint (msgPool pre) m
                   → StepPeer pre pid (peerStates pre pid) (m ∷ [])

 isCheat : ∀ {pre pid ms outs} → StepPeer pre pid ms outs → Set
 isCheat (step-honest _)  = ⊥
 isCheat (step-cheat _ _) = Unit

 initStatus : ∀ {pid pre ms outs}
            → StepPeer pre pid ms outs
            → InitStatus
            → InitStatus
 initStatus {pid} (step-honest _)  preinit = initd
 initStatus {pid} (step-cheat _ _) preinit = preinit

 -- Computes the post-sysstate for a given step-peer.
 StepPeer-post : ∀{pid st' outs}{pre : SystemState }
               → StepPeer pre pid st' outs → SystemState
 StepPeer-post {pid} {st'} {outs} {pre} sp = record pre
   { peerStates  = ⟦ peerStates pre  , pid ← st' ⟧
   ; initialised = ⟦ initialised pre , pid ← initStatus sp (initialised pre pid) ⟧
   ; msgPool     = List-map (pid ,_) outs ++ msgPool pre
   }

 StepPeer-post-lemma : ∀{pid st' outs}{pre : SystemState}
               → (pstep : StepPeer pre pid st' outs)
               → st' ≡ peerStates (StepPeer-post pstep) pid
 StepPeer-post-lemma pstep = sym override-target-≡

 StepPeer-post-lemma2 : ∀{pid}{pre : SystemState}{init' st outs}
                      → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) init' (st , outs))
                      → initialised (StepPeer-post {pid} {st} {outs} {pre} (step-honest sps)) pid ≡ initd
 StepPeer-post-lemma2 {pre = pre} _ = override-target-≡

 cheatStepDNMPeerStates : ∀{pid st' outs}{pre : SystemState}
                        → (theStep : StepPeer pre pid st' outs)
                        → isCheat theStep
                        → peerStates (StepPeer-post theStep) ≡ peerStates pre
 cheatStepDNMPeerStates {pid = pid} {pre = pre} (step-cheat _ _) _ = overrideSameVal-correct-ext {f = peerStates pre} {pid}

 cheatStepDNMInitialised : ∀{pid st' outs}{pre : SystemState}
                        → (theStep : StepPeer pre pid st' outs)
                        → isCheat theStep
                        → initialised (StepPeer-post theStep) ≡ initialised pre
 cheatStepDNMInitialised {pid = pid} {pre = pre} (step-cheat _ _) _ = overrideSameVal-correct-ext

 cheatStepDNMPeerStates₁ : ∀{pid pid' st' outs}{pre : SystemState}
                         → (theStep : StepPeer pre pid st' outs)
                         → isCheat theStep
                         → peerStates (StepPeer-post theStep) pid' ≡ peerStates pre pid'
 cheatStepDNMPeerStates₁ {pid} {pid'} (step-cheat fm x₁) x = overrideSameVal-correct pid pid'

 data Step : SystemState → SystemState → Set (ℓ+1 ℓ-PeerState) where
   step-peer : ∀{pid st' outs}{pre : SystemState}  -- TODO: eliminate if we're getting rid of epochs, merge with StepPeer
             → (pstep : StepPeer pre pid st' outs)
             → Step pre (StepPeer-post pstep)


 msgs-stable : ∀ {pre : SystemState} {post : SystemState} {m}
             → (theStep : Step pre post)
             → m ∈ msgPool pre
             → m ∈ msgPool post
 msgs-stable (step-peer {pid = pid} {outs = outs} _) m∈ = Any-++ʳ (List-map (pid ,_) outs) m∈

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
 ... | step-cheat _ _ = isInitd

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

 eventProcessorPostSt : ∀ {pid s' s outs init'} {st : SystemState}
                      → (r : ReachableSystemState st)
                      → (stP : StepPeerState pid (msgPool st) (initialised st)
                                             (peerStates st pid) init' (s' , outs))
                      → peerStates (StepPeer-post {pre = st} (step-honest stP)) pid ≡ s
                     → s ≡ s'
 eventProcessorPostSt _ _ ps≡s = trans (sym ps≡s) override-target-≡

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

 Any-Step-⇒ : ∀ {ℓ}{P Q : SystemStateRel {ℓ} Step}
            → (∀ {pre : SystemState}{post : SystemState} → (x : Step pre post) → P x → Q x)
            → ∀ {fst lst} {tr : Step* fst lst}
            → Any-Step {ℓ} P tr
            → Any-Step {ℓ} Q tr
 Any-Step-⇒ p⇒q (step-here cont {this} prf) = step-here cont (p⇒q this prf)
 Any-Step-⇒ p⇒q (step-there anyStep) = step-there (Any-Step-⇒ p⇒q anyStep)

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
 -- about who uses what keys for what parts (in our case, EpochConfigs either derived from genesis
 -- information or agreed during epoch changes).
 ValidSenderForPK-type : Set (ℓ+1 ℓ-VSFP ℓ⊔ ℓ-PeerState)
 ValidSenderForPK-type = PeerState → Part → PeerId → PK → Set ℓ-VSFP

 ValidSenderForPK-stable-type : ValidSenderForPK-type → Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
 ValidSenderForPK-stable-type vs4pk = ∀ {st part pk}{pid inits' ps' msgs}
                                      → ReachableSystemState st
                                      → StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) inits' (ps' , msgs)
                                      → initialised st pid ≡ initd
                                      → vs4pk (peerStates st pid) part pid pk
                                      → vs4pk ps'                 part pid pk

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
