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
  (Output        : Set)
  (PeerState     : Set)
  
  -- TODO: combine these into an "event handler" to be more consistent with PTFD?  I am not doing
  -- this for now because the Run.hs for LBFT assumes a fixed number of peers, and creates all of
  -- their states (EventProcessors) upfront before even telling them to initialize.  Ultimately we
  -- will need dynamic peers being created, different numbers of peers for different epochs, etc.
  -- The way I have this, new peers can initialize at any time, create their state, and send some
  -- messages.
  (CanInit       : Peer → Set)
  (Init          : (p : Peer) → CanInit p → PeerState × List Output)
  (MsgHandler    : (m : Message) → Instant → PeerState → PeerState × List Output)
  (OutputHandler : PeerState → Output → List Message)          -- Discerns whether action results in
                                                               -- sending a message.

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
  (Dishonest     : Message → Set)
  where

 -- We record the intended recipient of each message, which will be needed when we consider liveness
 -- because we will need to use assumptions about messages between honest peers being received
 -- within some time period (after GST).  However, for safety, we ignore the recipient and let any
 -- peer receive any message, regardless of intended recipient.  This is conservative, as anyone
 -- could redirect a message to someone else anyway.
 open LibraBFT.Global.Network.WithMsgType Message public

 record SystemState : Set where
   constructor sysState
   field
     sentMessages : SentMessages
     peerStates   : KVMap Peer PeerState
 open SystemState public

 initState : SystemState
 initState = sysState noMessages empty

 actionsToSends : PeerState → List Output → List Message
 actionsToSends st = concat ∘ List-map (OutputHandler st)

 sendMessage : ∀ {pre : SystemState} → Message → SystemState
 sendMessage {pre} msg = record pre { sentMessages = sendMsg (sentMessages pre) msg }

 sendMessagesFromOutputs : SystemState → PeerState → List Output → SentMessages
 sendMessagesFromOutputs st pst acts = foldr (flip sendMsg) (sentMessages st) (actionsToSends pst acts)

 allegedlySent : Message → SystemState → Set
 allegedlySent msg st = Dishonest msg ⊎ msg ∈SM sentMessages st

 -- All steps are for honest peers, except "cheat", which allows a peer to send any message it wants
 -- to anyone it wants, provided it is dishonest for that message.
 data Step (pre : SystemState): SystemState → Set where
   initPeer : (p : Peer)
            → (ts : Instant)
            → (canInit : CanInit p)
            → (ready : KVMap.lookup p (peerStates pre) ≡ nothing)
            → Step pre (sysState
                         (sendMessagesFromOutputs pre (proj₁ (Init p canInit)) (proj₂ (Init p canInit)))
                         (kvm-insert p (proj₁ (Init p canInit)) (peerStates pre) ready))

   recvMsg : ∀ {m : Message} {to : Peer} {ppre : PeerState} {ppost : PeerState} {acts : List Output}
             (p : Peer)
           → (ts : Instant)
           → allegedlySent m pre
           → (ready : KVMap.lookup p (peerStates pre) ≡ just ppre)
           → MsgHandler m ts ppre ≡ (ppost , acts)
           → Step pre (sysState
                         (sendMessagesFromOutputs pre ppost acts)
                         (kvm-update p ppost (peerStates pre) (maybe-⊥ ready)))

   cheat : ∀ (p : Peer)  -- TODO: Careful here!  Dishonest is now a function of only the message, since it contains the author.  Need to think about this.
             (ts : Instant)
             (m : Message)
         → Dishonest m
         → Step pre (sysState (sendMsg (sentMessages pre) m) (peerStates pre))

 isInitPeer : ∀ {pre post} → Step pre post → Set
 isInitPeer (initPeer _ _ _ _)  = ⊤
 isInitPeer (recvMsg _ _ _ _ _) = ⊥
 isInitPeer (cheat _ _ _ _)     = ⊥

 isInitPeer? : ∀ {pre post} → (theStep : Step pre post) → Dec (isInitPeer theStep)
 isInitPeer? {pre} {post} (initPeer _ _ _ _)  = yes tt
 isInitPeer? {pre} {post} (recvMsg _ _ _ _ _) = no id
 isInitPeer? {pre} {post} (cheat _ _ _ _)     = no id

 isRecvMsg : ∀ {pre post} → Step pre post → Set
 isRecvMsg (initPeer _ _ _ _)  = ⊥
 isRecvMsg (recvMsg _ _ _ _ _) = ⊤
 isRecvMsg (cheat _ _ _ _)     = ⊥

 isCheatStep : ∀ {pre post} → Step pre post → Set
 isCheatStep (initPeer _ _ _ _)  = ⊥
 isCheatStep (recvMsg _ _ _ _ _) = ⊥
 isCheatStep (cheat _ _ _ _)     = ⊤

 peerOf     : ∀ {pre post} → (theStep : Step pre post) → Peer
 peerOf     (initPeer p _ _ _)   = p
 peerOf     (recvMsg  p _ _ _ _) = p
 peerOf     (cheat p _ _ _)      = p

 rdyOf     : ∀ {pre post} → {theStep : Step pre post} → isInitPeer theStep → KVMap.lookup (peerOf theStep) (peerStates pre) ≡ nothing
 rdyOf     {theStep = initPeer _ _ _ rdy} _ = rdy

 ppreOf    : ∀ {pre post} → {theStep : Step pre post} → isRecvMsg theStep → PeerState
 ppreOf    {theStep = recvMsg {ppre = ppre} _ _ _ _  _} _ = ppre

 ppostOf    : ∀ {pre post} → {theStep : Step pre post} → isRecvMsg theStep → PeerState
 ppostOf    {theStep = recvMsg {ppost = ppost} _ _ _ _  _} _ = ppost

 -- TODO: rename to avoid confusion with rdy
 readyOf   : ∀ {pre post} → {theStep : Step pre post} → (isRecv : isRecvMsg theStep) → KVMap.lookup (peerOf theStep) (peerStates pre) ≡ just (ppreOf {theStep = theStep} isRecv)
 readyOf   {theStep = recvMsg p _ _ ready _} _ = ready

 msgOf   : ∀ {pre post} → {theStep : Step pre post} → (isRecv : isRecvMsg theStep) → Message
 msgOf   {theStep = recvMsg {m = m} _ _ _ _ _} _ = m

 actsOf   : ∀ {pre post} → {theStep : Step pre post} → (isRecv : isRecvMsg theStep) → List Output
 actsOf   {theStep = recvMsg {acts = acts} _ _ _ _ _} _ = acts

 canInitOf : ∀ {pre post} → {theStep : Step pre post} → isInitPeer theStep → CanInit (peerOf theStep)
 canInitOf {theStep = initPeer _ _ canInit _} _ = canInit

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

 InvariantStates≡ : ∀ {st} {st'} → (P : SystemState → Set) → st ≡ st' → P st → P st'
 InvariantStates≡ {st} {st'} P = subst P

 stepByOtherPreservesJ : ∀ {pre post p ppre ppost}
                       → (prop : (PeerState → Set))
                       → (theStep : Step pre post)
                       → (lookup p (peerStates pre))  ≡ just ppre
                       → (lookup p (peerStates post)) ≡ just ppost
                       → prop ppre
                       → ¬ prop ppost
                       → p ≡ peerOf theStep
 stepByOtherPreservesJ {pre}{sysState msgs' .(peerStates pre)}{p}{ppre}{ppost} prop (cheat by ts m x) ppre≡ ppost≡ preHolds postNotHold =
   ⊥-elim (postNotHold (subst prop (just-injective (trans (sym ppre≡) ppost≡)) preHolds))
 stepByOtherPreservesJ {pre}{post}{p}{ppre}{ppost} prop (initPeer by ts cI rdy) ppre≡ ppost≡ preHolds postNotHold =
   sym (insert-target-0 {k = by} {k' = p} {kvm = peerStates pre} {rdy} λ x₁ → ⊥-elim (postNotHold (subst prop (just-injective (trans (trans (sym ppre≡) x₁) ppost≡)) preHolds)))
 stepByOtherPreservesJ {pre}{post}{p}{ppre}{ppost} prop (recvMsg by ts x1 ready x2)  ppre≡ ppost≡ preHolds postNotHold =
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

 noChangePreservesState : ∀ {pre post}
                         → (theStep : Step pre post)
                         → (iR : isRecvMsg theStep)
                         → ppostOf iR ≡ ppreOf iR
                         → actsOf iR ≡ []
                         → pre ≡ post
 noChangePreservesState {pre} {post} (recvMsg {ppre = ppre} {ppost = ppost} {acts = acts} p ts ∈SM-pre ready run≡) iR ppost≡ acts≡
   with sym (lookup-correct-update-4 {rdy = maybe-⊥ ready} (trans ready (cong just (sym ppost≡))))
 ...| peerStates≡ rewrite acts≡ = cong (sysState (sentMessages pre)) peerStates≡ 

 -- If p's peerState is nothing in prestate and not nothing in the poststate, then the action is an initPeer by p and poststate has p's state as initial state

 initPeerLemma : ∀ {pre post p pst}
                 → {theStep : Step pre post}
                 → lookup p (peerStates pre) ≡ nothing
                 → lookup p (peerStates post) ≡ just pst
                 → peerOf theStep ≡ p × Σ (isInitPeer theStep)
                              (λ act → pst ≡ proj₁ (Init (peerOf theStep) (canInitOf act)))
 initPeerLemma {p = p} {theStep = cheat _ _ _ _} nothingBefore justAfter = ⊥-elim (maybe-⊥ justAfter nothingBefore)

 initPeerLemma {p = p} {theStep = theStep@(recvMsg by _ _ rdy _)} nothingBefore justAfter
    with by ≟Peer p
 ...| yes refl = ⊥-elim (maybe-⊥ rdy nothingBefore)
 ...| no neq rewrite stepByOtherPreservesPeerState theStep neq = ⊥-elim (maybe-⊥ justAfter nothingBefore)

 initPeerLemma {p = p} {theStep = theStep@(initPeer by _ _ rdy)} nothingBefore justAfter
    with by ≟Peer p
 ...| no  neq rewrite stepByOtherPreservesPeerState theStep neq = ⊥-elim (maybe-⊥ justAfter nothingBefore)
 ...| yes refl
    with insert-target {k = by} {k' = by} rdy ((flip maybe-⊥) nothingBefore) justAfter
 ...| _ , yyy = refl , tt , yyy

