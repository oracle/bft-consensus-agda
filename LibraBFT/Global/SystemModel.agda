{-# OPTIONS --allow-unsolved-metas #-}

open import Function using (flip ; const)

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types using (Meta)
open import LibraBFT.Concrete.Network as NM
open import LibraBFT.Global.Network
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap  -- TODO: move KVMap out of Concrete
open import LibraBFT.Concrete.OBM.RWST

open import Level

module LibraBFT.Global.SystemModel
  (Instant       : Set) -- How will we generate these.  Should the "system" do it?
  (Peer          : Set)
  (Message       : Set)
  (Signer        : WithSig Message)
  (Env           : Set)  -- Environment for RWST monad
  (Action        : Set)  -- What will RWST monad write?
  (PeerState     : Set)  -- State for RWST monad
  
  -- TODO: combine these into an "event handler" to be more consistent with PTFD?  I am not doing
  -- this for now because the Run.hs for LBFT assumes a fixed number of peers, and creates all of
  -- their states (EventProcessors) upfront before even telling them to initialize.  Ultimately we
  -- will need dynamic peers being created, different numbers of peers for different epochs, etc.
  -- The way I have this, new peers can initialize at any time, create their state, and send some
  -- messages.
  (Init          : Peer → Maybe (PeerState × List Action))
  (MsgHandler    : Message → Instant → RWST Env Action PeerState Unit)
  (ActionHandler : PeerState → Action → List (Peer × Message)) -- Discerns whether action results in
                                                               -- sending a message and to whom.

  -- The model will allow a peer to create and send any message it wants, if there is evidence that
  -- the peer is not honest.  But peers can be honest in some contexts and not honest in others.
  -- For example, BFT assumptions in LBFT are based on epochs, a peer may be an honest author in one
  -- epoch, but not another.  Therefore, the model should be instantiated with a way to determine
  -- whether an author would be honest if it sent a given message.  (In LBFT, messages contain
  -- epochIds, which can be used to determine who's honest when sending messages.)  Dishonest means
  -- the model allows for it to be not honest.  For example, an author of an epoch can be dishonest
  -- for messages in that epoch.  A non-author of the epoch is *not* considered dishonest for that
  -- epoch.  Its messages can be discarded.  We are concerned here with modeling an author that is
  -- allowed to send a message that doesn't follow the protocol.
  (Dishonest     : Message → Peer → Set)
  where

 -- We record the intended recipient of each message, which will be needed when we consider liveness
 -- because we will need to use assumptions about messages between honest peers being received
 -- within some time period (after GST).  However, for safety, we ignore the recipient and let any
 -- peer receive any message, regardless of intended recipient.  This is conservative, as anyone
 -- could redirect a message to someone else anyway.
 open LibraBFT.Global.Network.WithMsgType (Peer × Message)

 record SystemState : Set where
   constructor sysState
   field
     sentMessages : SentMessages
     peerStates   : KVMap Peer PeerState
 open SystemState

 initState : SystemState
 initState = sysState noMessages empty

 actionsToSends : PeerState → List Action → List (Peer × Message)
 actionsToSends st = concat ∘ List-map (ActionHandler st)

 postulate
   now : Instant

 sendMessage : ∀ {pre : SystemState} → Message → Peer → SystemState
 sendMessage {pre} msg p = record pre { sentMessages = sendMsg (sentMessages pre) (p , msg) }

 -- All steps are for honest peers, except "cheat", which allows a peer to send any message it wants
 -- to anyone it wants, provided it is dishonest for that message.
 data Step (pre : SystemState) {p : Peer} : SystemState → Set where
   initPeer : {ready : KVMap.lookup p (peerStates pre) ≡ nothing}
              {initp : PeerState × List Action}
            → Init p ≡ just initp
            → Step pre (sysState
                           (foldr (flip sendMsg) (sentMessages pre) (actionsToSends (proj₁ initp) (proj₂ initp)))
                           (kvm-insert p (proj₁ initp) (peerStates pre) ready))

   recvMsg : ∀ {m : Message} {to : Peer} {env : Env} {ppre : PeerState} {ppost : PeerState} {acts : List Action}
           → (to , m) ∈SM (sentMessages pre)
           → (ready : KVMap.lookup p (peerStates pre) ≡ just ppre)
           → RWST-run (MsgHandler m now) env ppre ≡ (unit , ppost , acts)
           → Step pre (sysState
                         (foldr (flip sendMsg) (sentMessages pre) (actionsToSends ppost acts))
                         (kvm-update p ppost (peerStates pre) (maybe-⊥ ready)))

   cheat : {m : Message} {to : Peer}
         → Dishonest m p
         → Step pre (sysState (sendMsg (sentMessages pre) (to , m)) (peerStates pre))

   -- TODO : we may need "spontaneous" actions that don't require a message to be received, for
   -- example timeout events?

 data ReachableSystemState : SystemState → Set where
   init : ReachableSystemState initState
   step : ∀ {preState postState} {p}
        → ReachableSystemState preState
        → Step preState {p} postState
        → ReachableSystemState postState
