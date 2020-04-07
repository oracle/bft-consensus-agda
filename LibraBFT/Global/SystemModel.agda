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

module LibraBFT.Global.SystemModel
  (Instant       : Set) -- How will we generate these.  Should the "system" do it?
  (Peer          : Set)
  (_≟Peer_       : ∀ (p₁ p₂ : Peer) → Dec (p₁ ≡ p₂))
  (Message       : Set)
  (Signer        : WithSig Message)
  (Action        : Set)
  (PeerState     : Set)
  (GetPK         : Message → PeerState → PK)
  
  -- TODO: combine these into an "event handler" to be more consistent with PTFD?  I am not doing
  -- this for now because the Run.hs for LBFT assumes a fixed number of peers, and creates all of
  -- their states (EventProcessors) upfront before even telling them to initialize.  Ultimately we
  -- will need dynamic peers being created, different numbers of peers for different epochs, etc.
  -- The way I have this, new peers can initialize at any time, create their state, and send some
  -- messages.
  (CanInit       : Peer → Set)
  (Init          : (p : Peer) → CanInit p → PeerState × List Action)
  (MsgHandler    : (m : Message) → Maybe (WithVerSig {Message} ⦃ Signer ⦄ m) → Instant → PeerState → PeerState × List Action)
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
 open LibraBFT.Global.Network.WithMsgType (Peer × Message) public

 record SystemState : Set where
   constructor sysState
   field
     sentMessages : SentMessages
     peerStates   : KVMap Peer PeerState
 open SystemState public

 initState : SystemState
 initState = sysState noMessages empty

 actionsToSends : PeerState → List Action → List (Peer × Message)
 actionsToSends st = concat ∘ List-map (ActionHandler st)

 sendMessage : ∀ {pre : SystemState} → Message → Peer → SystemState
 sendMessage {pre} msg p = record pre { sentMessages = sendMsg (sentMessages pre) (p , msg) }

 sendMessagesFromActions : SystemState → PeerState → List Action → SentMessages
 sendMessagesFromActions st pst acts = foldr (flip sendMsg) (sentMessages st) (actionsToSends pst acts)

 -- All steps are for honest peers, except "cheat", which allows a peer to send any message it wants
 -- to anyone it wants, provided it is dishonest for that message.
 data Step (pre : SystemState): SystemState → Set where
   initPeer : (p : Peer)
            → (ts : Instant)
            → (canInit : CanInit p)
            → (ready : KVMap.lookup p (peerStates pre) ≡ nothing)
            → Step pre (sysState
                         (sendMessagesFromActions pre (proj₁ (Init p canInit)) (proj₂ (Init p canInit)))
                         (kvm-insert p (proj₁ (Init p canInit)) (peerStates pre) ready))

   recvMsg : ∀ {m : Message} {to : Peer} {ppre : PeerState} {ppost : PeerState} {acts : List Action}
             (p : Peer)
           → (ts : Instant)
           → (to , m) ∈SM (sentMessages pre)
           → (ready : KVMap.lookup p (peerStates pre) ≡ just ppre)
           → (verMB : Maybe (WithVerSig ⦃ Signer ⦄ m))
           → verMB ≡ check-signature ⦃ Signer ⦄ (GetPK m ppre) m
           → MsgHandler m verMB ts ppre ≡ (ppost , acts)
           → Step pre (sysState
                         (sendMessagesFromActions pre ppost acts)
                         (kvm-update p ppost (peerStates pre) (maybe-⊥ ready)))

   cheat : ∀ (p : Peer)
             (ts : Instant)
             (to : Peer) (m : Message)
         → Dishonest m p
         → Step pre (sysState (sendMsg (sentMessages pre) (to , m)) (peerStates pre))

 isInitPeer : ∀ {pre post} → Step pre post → Set
 isInitPeer (initPeer _ _ _ _)      = ⊤
 isInitPeer (recvMsg _ _ _ _ _ _ _) = ⊥
 isInitPeer (cheat _ _ _ _ _)       = ⊥

 isInitPeer? : ∀ {pre post} → (theStep : Step pre post) → Dec (isInitPeer theStep)
 isInitPeer? {pre} {post} (initPeer _ _ _ _)      = yes tt
 isInitPeer? {pre} {post} (recvMsg _ _ _ _ _ _ _) = no id
 isInitPeer? {pre} {post} (cheat _ _ _ _ _)       = no id

 isRecvMsg : ∀ {pre post} → Step pre post → Set
 isRecvMsg (initPeer _ _ _ _)      = ⊥
 isRecvMsg (recvMsg _ _ _ _ _ _ _) = ⊤
 isRecvMsg (cheat _ _ _ _ _)       = ⊥

 isCheatStep : ∀ {pre post} → Step pre post → Set
 isCheatStep (initPeer _ _ _ _)      = ⊥
 isCheatStep (recvMsg _ _ _ _ _ _ _) = ⊥
 isCheatStep (cheat _ _ _ _ _)       = ⊤

 peerOf     : ∀ {pre post} → (theStep : Step pre post) → Peer
 peerOf     (initPeer p _ _ _)       = p
 peerOf     (recvMsg  p _ _ _ _ _ _) = p
 peerOf     (cheat p _ _ _ _)        = p

 rdyOf     : ∀ {pre post} → (theStep : Step pre post) → isInitPeer theStep → KVMap.lookup (peerOf theStep) (peerStates pre) ≡ nothing
 rdyOf     (initPeer _ _ _ rdy) _ = rdy

 canInitOf : ∀ {pre post} → (theStep : Step pre post) → isInitPeer theStep → CanInit (peerOf theStep)
 canInitOf (initPeer _ _ canInit _) _ = canInit

 -- TODO : we may need "spontaneous" actions that don't require a message to be received, for
 -- example timeout events?

 data ReachableSystemState : SystemState → Set where
   init : ReachableSystemState initState
   step : ∀ {preState postState}
        → ReachableSystemState preState
        → Step preState postState
        → ReachableSystemState postState

 Invariant : (SystemState → Set) → Set
 Invariant P = ∀ {s : SystemState} → ReachableSystemState s → P s

 stepByOtherPreservesJ : ∀ {pre post p ppre ppost}
                       → (prop : (PeerState → Set))
                       → (theStep : Step pre post)
                       → (lookup p (peerStates pre))  ≡ just ppre
                       → (lookup p (peerStates post)) ≡ just ppost
                       → prop ppre
                       → ¬ prop ppost
                       → p ≡ peerOf theStep
 stepByOtherPreservesJ {pre}{sysState msgs' .(peerStates pre)}{p}{ppre}{ppost} prop (cheat by ts to m x) ppre≡ ppost≡ preHolds postNotHold =
   ⊥-elim (postNotHold (subst prop (just-injective (trans (sym ppre≡) ppost≡)) preHolds))
 stepByOtherPreservesJ {pre}{post}{p}{ppre}{ppost} prop (initPeer by ts cI rdy) ppre≡ ppost≡ preHolds postNotHold =
   sym (insert-target-0 {k = by} {k' = p} {kvm = peerStates pre} {rdy} λ x₁ → ⊥-elim (postNotHold (subst prop (just-injective (trans (trans (sym ppre≡) x₁) ppost≡)) preHolds)))
 stepByOtherPreservesJ {pre}{post}{p}{ppre}{ppost} prop (recvMsg by ts x1 ready verMB refl x2)  ppre≡ ppost≡ preHolds postNotHold =
   sym (update-target {kvm = peerStates pre}{k1 = p} {k2 = by} λ x → postNotHold (subst prop (just-injective (trans (trans (sym ppre≡) x) ppost≡)) preHolds))

{-
 -- Not used, not updated for purely relational Step definition
 stepDoesNotInitialize : ∀ {pre post postReach p}
                       → {theStep : Step pre post}
                       → {preReach : ReachableSystemState pre}
                       → lookup p (peerStates pre) ≡ nothing
                       → postReach ≡ step {pre} {post} preReach theStep
                       → isInitPeer theStep ⊎ lookup p (peerStates post) ≡ nothing
 stepDoesNotInitialize                           {theStep = initPeer} nothingBefore refl = inj₁ tt
 stepDoesNotInitialize                           {theStep = cheat x} nothingBefore refl = inj₂ nothingBefore
 stepDoesNotInitialize {pre} {post} {p = p} {theStep = recvMsg x1 x2 x3} nothingBefore refl
   with (lookup p) (peerStates post) | inspect (lookup p) (peerStates post)
 ...| nothing | [ xx1 ] = inj₂ refl
 ...| just jv | [ xx1 ] = ⊥-elim (xx (update-target {k1 = p} {k2 = by} nothingBefore λ x → maybe-⊥ xx1 x))
-}

 postulate  -- TODO: prove
   msgs-stable : ∀ {pre post m}
                 → (theStep : Step pre post)
                 → m ∈SM sentMessages pre
                 → m ∈SM sentMessages post

   cheatPreservesPeerState : ∀ {pre post p}
                           → (theStep : Step pre post)
                           → isCheatStep theStep
                           → lookup p (peerStates post) ≡ lookup p (peerStates pre)

   stepByOtherPreservesPeerState : ∀ {pre post p}
                           → (theStep : Step pre post)
                           → ¬ (peerOf theStep ≡ p)
                           → lookup p (peerStates post) ≡ lookup p (peerStates pre)

 -- If p's peerState is nothing in prestate and not nothing in the poststate, then the action is an initPeer by p and poststate has p's state as initial state

 initPeerLemma : ∀ {pre post p pst}
                 → {theStep : Step pre post}
                 → lookup p (peerStates pre) ≡ nothing
                 → lookup p (peerStates post) ≡ just pst
                 → peerOf theStep ≡ p × Σ (isInitPeer theStep)
                              (λ act → pst ≡ proj₁ (Init (peerOf theStep) (canInitOf theStep act)))
 initPeerLemma {p = p} {theStep = cheat _ _ _ _ _} nothingBefore justAfter = ⊥-elim (maybe-⊥ justAfter nothingBefore)

 initPeerLemma {p = p} {theStep = theStep@(recvMsg by _ _ rdy _ _ _)} nothingBefore justAfter
    with by ≟Peer p
 ...| yes refl = ⊥-elim (maybe-⊥ rdy nothingBefore)
 ...| no neq rewrite stepByOtherPreservesPeerState theStep neq = ⊥-elim (maybe-⊥ justAfter nothingBefore)

 initPeerLemma {p = p} {theStep = theStep@(initPeer by _ _ rdy)} nothingBefore justAfter
    with by ≟Peer p
 ...| no  neq rewrite stepByOtherPreservesPeerState theStep neq = ⊥-elim (maybe-⊥ justAfter nothingBefore)
 ...| yes refl
    with insert-target {k = by} {k' = by} rdy ((flip maybe-⊥) nothingBefore) justAfter
 ...| _ , yyy = refl , tt , yyy

