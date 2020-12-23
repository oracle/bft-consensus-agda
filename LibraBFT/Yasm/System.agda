{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Types -- TODO-2: remove this, see comment below

open import LibraBFT.Yasm.AvailableEpochs using (AvailableEpochs) renaming (lookup'' to EC-lookup)
import LibraBFT.Yasm.AvailableEpochs as AE

open import LibraBFT.Yasm.Base

-- This module defines a model of a distributed system, parameterized by
-- SystemParameters, which establishes various application-dependent types,
-- handlers, etc.  The model supports a set of peers executing handlers in
-- response to messages received; these handlers can update the peer's
-- local state and/or send additional messages.  The model also enables
-- "cheat" steps, which can send arbitrary messages, except that they are
-- constrained to prevent a cheat step from introducing a new signature for
-- an "honest" public key.  The module also contains some structures for
-- proving properties of executions of the modeled system.

module LibraBFT.Yasm.System (parms : SystemParameters) where
 open SystemParameters parms

 -- TODO-2: The System model currently depends on a specific EpochConfig
 -- type, which is imported from LibraBFT-specific types.  However, the
 -- system model should be entirely application-independent.  Therefore, we
 -- should factor EpochConfig out of Yasm, and have the SystemParameters
 -- include an EpochConfig type and a way to query whether a given peer is
 -- a member of the represented epoch, and if so, with what associated PK.
 open EpochConfig

 PeerId : Set -- TODO-2: When we factor EpochConfig out of here (see
              -- comment above), PeerId will be a parameter to
              -- SystemParameters; for now, it's NodeId to make it
              -- compatible with everything else.
 PeerId = NodeId

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
 record SystemState (e : ℕ) : Set where
   field
     peerStates  : Map PeerId PeerState
     msgPool     : SentMessages          -- All messages ever sent
     availEpochs : AvailableEpochs e
 open SystemState public

 initialState : SystemState 0
 initialState = record
   { peerStates  = Map-empty
   ; msgPool     = []
   ; availEpochs = []
   }

 -- Convenience function for appending an epoch to the system state
 pushEpoch : ∀{e} → EpochConfigFor e → SystemState e → SystemState (suc e)
 pushEpoch 𝓔 st = record
   { peerStates  = peerStates st
   ; msgPool     = msgPool st
   ; availEpochs = AE.append 𝓔 (availEpochs st)
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
 data StepPeerState {e}(pid : PeerId)(𝓔s : AvailableEpochs e)(pool : SentMessages)
          : Maybe PeerState → PeerState → List Msg → Set where
   -- The peer receives an "initialization package"; for now, this consists
   -- of the actual EpochConfig for the epoch being initialized.  Later, we
   -- may move to a more general scheme, enabled by assuming a function
   -- 'render : InitPackage -> EpochConfig'.
   step-init : ∀{ms s' out}(ix : Fin e)
             → (s' , out) ≡ init pid (AE.lookup' 𝓔s ix) ms
             → StepPeerState pid 𝓔s pool ms s' out

   -- The peer processes a message in the pool
   step-msg  : ∀{m ms s s' out}
             → m ∈ pool
             → ms ≡ just s → (s' , out) ≡ handle pid (proj₂ m) s
             → StepPeerState pid 𝓔s pool ms s' out

 -- The pre-state of the suplied PeerId is related to the post-state and list of output messages iff:
 data StepPeer {e}(pre : SystemState e) : PeerId → Maybe PeerState → List Msg → Set where
   -- it can be obtained by a handle or init call.
   step-honest : ∀{pid st outs}
               → StepPeerState pid (availEpochs pre) (msgPool pre) (Map-lookup pid (peerStates pre)) st outs
               → StepPeer pre pid (just st) outs

   -- or the peer decides to cheat.  CheatMsgConstraint ensures it cannot
   -- forge signatures by honest peers.  Cheat steps do not modify peer
   -- state: these are maintained exclusively by the implementation
   -- handlers.
   step-cheat  : ∀{pid}
               → (fm : SentMessages → Maybe PeerState → Msg)
               → let m = fm (msgPool pre) (Map-lookup pid (peerStates pre))
                  in CheatMsgConstraint (msgPool pre) m
                   → StepPeer pre pid (Map-lookup pid (peerStates pre)) (m ∷ [])

 isCheat : ∀ {e pre pid ms outs} → StepPeer {e} pre pid ms outs → Set
 isCheat (step-honest _)  = ⊥
 isCheat (step-cheat _ _) = Unit

 -- Computes the post-sysstate for a given step-peer.
 StepPeer-post : ∀{e pid st' outs}{pre : SystemState e}
               → StepPeer pre pid st' outs → SystemState e
 StepPeer-post {e} {pid} {st'} {outs} {pre} _ = record pre
   { peerStates = Map-set pid st' (peerStates pre)
   ; msgPool    = List-map (pid ,_) outs ++ msgPool pre
   }

 data Step : ∀{e e'} → SystemState e → SystemState e' → Set where
   step-epoch : ∀{e}{pre : SystemState e}
              → (𝓔 : EpochConfigFor e)
              -- TODO-3: Eventually, we'll condition this step to only be
              -- valid when peers on the previous epoch have agreed that 𝓔
              -- is the new one.  → ∃EnoughValidCommitMsgsFor pre 𝓔
              → Step pre (pushEpoch 𝓔 pre)

   step-peer : ∀{e pid st' outs}{pre : SystemState e}
             → (pstep : StepPeer pre pid st' outs)
             → Step pre (StepPeer-post pstep)

 postulate -- TODO-1: prove it
   msgs-stable : ∀ {e e'} {pre : SystemState e} {post : SystemState e'} {m}
               → (theStep : Step pre post)
               → m ∈ msgPool pre
               → m ∈ msgPool post

 postulate -- not used yet, but some proofs could probably be cleaned up using this,
           -- e.g., prevVoteRnd≤-pred-step in Impl.VotesOnce
   sendMessages-target : ∀ {m : SenderMsgPair} {sm : SentMessages} {ml : List SenderMsgPair}
                       → ¬ (m ∈ sm)
                       → m ∈ (ml ++ sm)
                       → m ∈ ml

 step-epoch-does-not-send : ∀ {e} (pre : SystemState e) (𝓔 : EpochConfigFor e)
                            → msgPool (pushEpoch 𝓔 pre) ≡ msgPool pre
 step-epoch-does-not-send _ _ = refl

 -- * Reflexive-Transitive Closure

 data Step* : ∀{e e'} → SystemState e → SystemState e' → Set where
   step-0 : ∀{e}{pre : SystemState e}
          → Step* pre pre

   step-s : ∀{e e' e''}{fst : SystemState e}{pre : SystemState e'}{post : SystemState e''}
          → Step* fst pre
          → Step pre post
          → Step* fst post

 ReachableSystemState : ∀{e} → SystemState e → Set
 ReachableSystemState = Step* initialState

 Step*-mono : ∀{e e'}{st : SystemState e}{st' : SystemState e'}
            → Step* st st' → e ≤ e'
 Step*-mono step-0 = ≤-refl
 Step*-mono (step-s tr (step-peer _)) = Step*-mono tr
 Step*-mono (step-s tr (step-epoch _)) = ≤-step (Step*-mono tr)

 MsgWithSig∈-Step* : ∀{e e' sig pk}{st : SystemState e}{st' : SystemState e'}
                   → Step* st st'
                   → MsgWithSig∈ pk sig (msgPool st)
                   → MsgWithSig∈ pk sig (msgPool st')
 MsgWithSig∈-Step* step-0        msig = msig
 MsgWithSig∈-Step* (step-s tr (step-epoch _)) msig
   = MsgWithSig∈-Step* tr msig
 MsgWithSig∈-Step* (step-s tr (step-peer ps)) msig
   = MsgWithSig∈-++ʳ (MsgWithSig∈-Step* tr msig)

 MsgWithSig∈-Step*-part : ∀{e e' sig pk}{st : SystemState e}{st' : SystemState e'}
                        → (tr   : Step* st st')
                        → (msig : MsgWithSig∈ pk sig (msgPool st))
                        → msgPart msig ≡ msgPart (MsgWithSig∈-Step* tr msig)
 MsgWithSig∈-Step*-part step-0        msig = refl
 MsgWithSig∈-Step*-part (step-s tr (step-epoch _)) msig
   = MsgWithSig∈-Step*-part tr msig
 MsgWithSig∈-Step*-part (step-s tr (step-peer ps)) msig
   = MsgWithSig∈-Step*-part tr msig

 ------------------------------------------

 -- Type synonym to express a relation over system states;
 SystemStateRel : (∀{e e'} → SystemState e → SystemState e' → Set) → Set₁
 SystemStateRel P = ∀{e e'}{st : SystemState e}{st' : SystemState e'} → P st st' → Set

 -- Just like Data.List.Any maps a predicate over elements to a predicate over lists,
 -- Any-step maps a relation over steps to a relation over steps in a trace.
 data Any-Step (P : SystemStateRel Step) : SystemStateRel Step* where
  step-here  : ∀{e e' e''}{fst : SystemState e}{pre : SystemState e'}{post : SystemState e''}
             → (cont : Step* fst pre)
             → {this : Step pre post}(prf  : P this)
             → Any-Step P (step-s cont this)

  step-there : ∀{e e' e''}{fst : SystemState e}{pre : SystemState e'}{post : SystemState e''}
             → {cont : Step* fst pre}
             → {this : Step pre post}
             → (prf  : Any-Step P cont)
             → Any-Step P (step-s cont this)

 Any-Step-⇒ : ∀ {P Q : SystemStateRel Step}
            → (∀ {e e'}{pre : SystemState e}{post : SystemState e'} → (x : Step pre post) → P {e} {e'} x → Q {e} {e'} x)
            → ∀ {e e' fst lst} {tr : Step* {e} {e'} fst lst}
            → Any-Step P tr
            → Any-Step Q tr
 Any-Step-⇒ p⇒q (step-here cont {this} prf) = step-here cont (p⇒q this prf)
 Any-Step-⇒ p⇒q (step-there anyStep) = step-there (Any-Step-⇒ p⇒q anyStep)

 Any-Step-elim
   : ∀{e₀ e₁}{st₀ : SystemState e₀}{st₁ : SystemState e₁}{P : SystemStateRel Step}{Q : Set}
   → {r : Step* st₀ st₁}
   → (P⇒Q : ∀{d d'}{s : SystemState d}{s' : SystemState d'}{st : Step s s'}
          → P st → Step* s' st₁ → Q)
   → Any-Step P r → Q
 Any-Step-elim P⇒Q (step-here cont prf)
   = P⇒Q prf step-0
 Any-Step-elim P⇒Q (step-there {this = this} f)
   = Any-Step-elim (λ p s → P⇒Q p (step-s s this)) f

 ------------------------------------------

 module _ (P : ∀{e} → SystemState e → Set) where

   Step*-Step-fold : (∀{e}{st : SystemState e}
                        → ReachableSystemState st
                        → (𝓔 : EpochConfigFor e)
                        → P st
                        → P (pushEpoch 𝓔 st))
                   → (∀{e pid st' outs}{st : SystemState e}
                        → ReachableSystemState st
                        → (pstep : StepPeer st pid st' outs)
                        → P st
                        → P (StepPeer-post pstep))
                   → P initialState
                   → ∀{e}{st : SystemState e}
                   → (tr : ReachableSystemState st) → P st
   Step*-Step-fold fe fs p₀ step-0 = p₀
   Step*-Step-fold fe fs p₀ (step-s tr (step-epoch 𝓔)) = fe tr 𝓔 (Step*-Step-fold fe fs p₀ tr)
   Step*-Step-fold fe fs p₀ (step-s tr (step-peer p)) = fs tr p (Step*-Step-fold fe fs p₀ tr)
