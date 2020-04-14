{-# OPTIONS --allow-unsolved-metas #-}

open import Function using (flip ; const)

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types using (Meta)
open import LibraBFT.Global.Network
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap -- TODO: move KVMap out of Concrete
open import LibraBFT.Concrete.OBM.RWST

open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

module LibraBFT.Global.SystemModel (#peers : ℕ) where
 {- 

 VCM: I removed a number of things from the abstract model
 to see how it would turn out; I outline the reasons below:

 1. Remove Instant; I have no idea why its needed and it only shows
 up as an extra parameter everywhere it appears.

 2. Make peers into a natural number; the system state can then contain
 a vector of PeerState and we don't need to handle Maybe's everywhere.

 3. Remove the Action type altogether; the RWST monad will be useful
 when we are translating Haskell code; here, it is way more useful
 to look at peers as a function from Env, State and Msg to
 new state and list of Msgs to send. This is what we do anywayt with
 'sendMessagesFromActions'

 4. Removed canInit and Init; peers will all start together for the
 time being and all start with the same initial state. If we ever need
 'initialization messages', we can encoded that in the state transtitino
 of the peer. I'd argue that epoch changes ahd peer changes are a great
 problem to have in the future, but would focus on proving properties
 for a fixed set initially.

 -}

 Peer : Set
 Peer = Fin #peers
 -- When we come to need dishonest peers, we'll do smthing like:
 -- Peer = Fin (#hpeers + #dpeers)

 module WithParms 
  -- Messages to be sent accross
  (Message       : Set)
  -- These messages must be carry signatures,
  -- (Signer        : WithSig Message) -- VCM: unecessary here!
  -- (Honest?) peers will keep a value of type PeerState as their state.
  -- The initial state is PeerState₀.
  (PeerState     : Set)  
  (PeerState₀    : Peer → PeerState)
  (stepPeer      : PeerState → Message → (List (Peer × Message) × PeerState))
    where

  -- We record the intended recipient of each message, which will be
  -- needed when we consider liveness because we will need to use
  -- assumptions about messages between honest peers being received within
  -- some time period (after GST).  However, for safety, we ignore the
  -- recipient and let any peer receive any message, regardless of
  -- intended recipient.  This is conservative, as anyone could redirect a
  -- message to someone else anyway.
  open LibraBFT.Global.Network.WithMsgType (Peer × Message) public

  record SysState : Set where
    constructor sysState
    field
      sentMessages : SentMessages
      peerStates   : Vec PeerState #peers
      -- VCM: Instead of instant, we can keep a counter on the system
      -- state and annotate each message with a message-order if
      -- we ever come to need to talk about order of sendnig;
      -- I think it makes no sense though, because the time which messages
      -- have been sent should not influence correctness of the algorithm.
      -- Maybe we'll use it for liveness, but then again, I'd suggest 
      -- we wait until then to complicate the model with this.
  open SysState public

  SysState₀ : SysState
  SysState₀ = sysState noMessages (Vec-tabulate PeerState₀)

  peerState : SysState → Peer → PeerState
  peerState sys = Vec-lookup (peerStates sys)

  sysUpdate : Peer → Message → SysState → SysState
  sysUpdate p msg (sysState msgs peerSts)
    = let (outs , st') = stepPeer (Vec-lookup peerSts p) msg
       in sysState (sendMsgs msgs outs) 
                   (Vec-updateAt p (const st') peerSts)

  -- The step relation is significantly simpler; granted, I didn't
  -- add cheating steps yet, but they will also be simple
  data SysStep (sys : SysState) : SysState → Set where
    peerStep : (p : Peer)(m : Message)
             → (p , m) ∈SM sentMessages sys
             → SysStep sys (sysUpdate p m sys)

    -- TODO: add cheating!

  whichPeer : ∀{pre post} → SysStep pre post → Peer
  whichPeer (peerStep p _ _) = p

  whichMsg : ∀{pre post} → SysStep pre post → Message
  whichMsg (peerStep _ m _) = m

  msgs-stable : ∀ {pre post m} → SysStep pre post
              → m ∈SM sentMessages pre
              → m ∈SM sentMessages post
  msgs-stable {pre} (peerStep p msg p∈msgs) hyp 
    = let (outs , st') = stepPeer (Vec-lookup (peerStates pre) p) msg
       in ∈SM-stable-list outs hyp

  states-stable : ∀{pre post} → (e : SysStep pre post)
                → ∃[ st' ] (peerStates post ≡ Vec-updateAt (whichPeer e) (const st') (peerStates pre))
  states-stable {pre} (peerStep p msg p∈msgs) 
    = let (outs , st') = stepPeer (Vec-lookup (peerStates pre) p) msg
       in st' , refl

  peerState-stable : ∀{pre post}
                   → (e : SysStep pre post)
                   → (p : Peer) → p ≢ whichPeer e
                   → peerState post p ≡ peerState pre p
  peerState-stable e p hyp = {!!}

  -- Reflexive Transitive closure
  SysStep* : SysState → SysState → Set
  SysStep* = Star SysStep

  -- A reachable state is related to the initial state
  -- through the reflexive transivie closure of SysStep.
  ReachableSysState : SysState → Set
  ReachableSysState s = SysStep* SysState₀ s

  Invariant : (SysState → Set) → Set
  Invariant P = ∀{s : SysState} → ReachableSysState s → P s



{-
    cheatPreservesPeerState : ∀ {pre post by p ts}
                            → (theStep : Step by pre ts post)
                            → isCheatStep theStep
                            → lookup p (peerStates post) ≡ lookup p (peerStates pre)

    stepByOtherPreservesPeerState : ∀ {pre post by p ts}
                            → (theStep : Step by pre ts post)
                            → ¬ (by ≡ p)
                            → lookup p (peerStates post) ≡ lookup p (peerStates pre)

-}
{-
  

  data ReachableSysState : SysState → Set where
    zero : ReachableSysState initState
    step : ∀ {
         → ReachableSystemState preState
         → ∀ {p}
         → Step p preState ts postState
         → ReachableSystemState postState

-}
