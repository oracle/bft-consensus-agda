{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.OBM.RWST
open import LibraBFT.Concrete.Util.KVMap
open import Optics.All

module LibraBFT.Example.Example where

{--

 Here we model a super simple distributed system, in which a peer
 can send a message with a value that is one higher than a message
 previously sent by an honest peer.  A peer can also "announce" a
 value, provided some honest peer has sent all previous values.
 There can be one dishonest peer, so an honest peer must see the
 same value from two different peers before being convinced that
 it has been sent by one honest peer.  The correctness condition
 is that if a value has been announced, then it and all smaller
 values have been sent by an honest peer.

--}

 Instant : Set
 Instant = ℕ

 PeerId : Set
 PeerId = ℕ

 postulate
   fakePubKey : ℕ → PK
   fakePubKey-inj : ∀ {a1 a2} → fakePubKey a1 ≡ fakePubKey a2 → a1 ≡ a2

 _≟-PeerId_ : (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
 _≟-PeerId_ = _≟_

 data Message : Set

 record DirectMessage : Set where
   constructor mkDirectMessage
   field
     :author : PeerId
     :val    : ℕ
     :sigMB  : Maybe Signature
 open DirectMessage

 unquoteDecl author   val   sigMB = mkLens (quote DirectMessage)
            (author ∷ val ∷ sigMB ∷ [])

 record GossipMessage : Set where
   constructor mkGossipMessage
   field
     :original : DirectMessage
     :gmAuthor : PeerId
     :gmSigMB  : Maybe Signature
 open GossipMessage

 unquoteDecl original   gmAuthor   gmSigMB = mkLens (quote GossipMessage)
            (original ∷ gmAuthor ∷ gmSigMB ∷ [])

 data Message where
   direct : DirectMessage → Message
   gossip : GossipMessage → Message

 getAuthor : Message → PeerId
 getAuthor (direct m) = m ^∙ author
 getAuthor (gossip m) = m ^∙ gmAuthor

 getPubKey : Message → PK
 getPubKey = fakePubKey ∘ getAuthor

 data Output : Set where
   announce : ℕ → Output           -- This is analogous to "commit"
   send     : ℕ → PeerId → Output

 record State : Set where
   constructor mkState
   field
     :myId         : PeerId
     :myPubKey     : PK
     :maxSeen      : ℕ
     :newValSender : Maybe PeerId
 open State

 unquoteDecl myId   myPubKey   maxSeen   newValSender = mkLens (quote State)
            (myId ∷ myPubKey ∷ maxSeen ∷ newValSender ∷ [])

 canInit : PeerId → Set
 canInit p = ⊤

 initialStateAndMessages : (p : PeerId) → canInit p → State × List Output
 initialStateAndMessages p _ = mkState p (fakePubKey p) 0 nothing , []  -- TODO : send something!

 instance
   sig-DirectMessage : WithSig DirectMessage
   sig-DirectMessage = record
      { Signed         = Is-just ∘ :sigMB
      ; isSigned?      = λ m → Maybe-Any-dec (λ _ → yes tt) (m ^∙ sigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ dm → concat ( encode (dm ^∙ author)
                                       ∷ encode (dm ^∙ val)
                                       ∷ [])
      }

   sig-GossipMessage : WithSig GossipMessage
   sig-GossipMessage = record
      { Signed         = Is-just ∘ :gmSigMB
      ; isSigned?      = λ m → Maybe-Any-dec (λ _ → yes tt) (m ^∙ gmSigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ gm → concat ( encode ((gm ^∙ original) ^∙ author)
                                       ∷ encode ((gm ^∙ original) ^∙ val)
                                       ∷ encode ((gm ^∙ original) ^∙ sigMB)
                                       ∷ [])
      }

 open RWST-do

 data HandlerResult : Set where
   noChange         : HandlerResult
   gotFirstAdvance  : PeerId → HandlerResult
   confirmedAdvance : ℕ → HandlerResult

 isGotFirstAdvance : HandlerResult → Maybe PeerId
 isGotFirstAdvance noChange             = nothing
 isGotFirstAdvance (confirmedAdvance _) = nothing
 isGotFirstAdvance (gotFirstAdvance n)  = just n

 isGotFirstAdvance≡ : {hR : HandlerResult}{p : PeerId}
                    → isGotFirstAdvance hR ≡ just p
                    → hR ≡ gotFirstAdvance p
 isGotFirstAdvance≡ {gotFirstAdvance p'} hRj = cong gotFirstAdvance (just-injective hRj)

 isConfirmedAdvance : HandlerResult → Maybe ℕ
 isConfirmedAdvance  noChange            = nothing
 isConfirmedAdvance (confirmedAdvance n) = just n
 isConfirmedAdvance (gotFirstAdvance _)  = nothing

 isConfirmedAdvance≡ : {hR : HandlerResult}{n : ℕ}
                     → isConfirmedAdvance hR ≡ just n
                     → hR ≡ confirmedAdvance n
 isConfirmedAdvance≡ {confirmedAdvance n'} hRj = cong confirmedAdvance (just-injective hRj)

 gFA≢cA : ∀ {p n} → gotFirstAdvance p ≢ confirmedAdvance n
 gFA≢cA ()

 nC≢gFA : ∀ {p} → noChange ≢ gotFirstAdvance p
 nC≢gFA ()

 nC≢cA : ∀ {v} → noChange ≢ confirmedAdvance v
 nC≢cA ()

 handlerResultIsSomething : {hR : HandlerResult}
                          → isConfirmedAdvance hR ≡ nothing
                          → isGotFirstAdvance  hR ≡ nothing
                          → hR ≡ noChange
 handlerResultIsSomething {noChange} _ _ = refl

 gFA-injective : ∀ {n m} → gotFirstAdvance n ≡ gotFirstAdvance m → n ≡ m
 gFA-injective refl = refl

 cA-injective : ∀ {n m} → confirmedAdvance n ≡ confirmedAdvance m → n ≡ m
 cA-injective refl = refl

 _≟HR_ : (hr1 hr2 : HandlerResult) → Dec (hr1 ≡ hr2)
 noChange             ≟HR (confirmedAdvance _) = no λ ()
 noChange             ≟HR (gotFirstAdvance  _) = no λ ()
 noChange             ≟HR noChange             = yes refl
 (gotFirstAdvance  _) ≟HR noChange             = no λ ()
 (confirmedAdvance _) ≟HR noChange             = no λ ()
 (gotFirstAdvance  _) ≟HR (confirmedAdvance _) = no λ ()
 (confirmedAdvance _) ≟HR (gotFirstAdvance  _) = no λ ()
 (gotFirstAdvance p1) ≟HR (gotFirstAdvance p2) with p1 ≟ p2
 ...| yes refl = yes refl
 ...| no  neq  = no (neq ∘ gFA-injective)
 (confirmedAdvance v1) ≟HR (confirmedAdvance v2) with v1 ≟ v2
 ...| yes refl = yes refl
 ...| no  neq  = no (neq ∘ cA-injective)

 -- TODO: none of the Dec proofs are used here; can this be simplified?
 pureHandler : (msg : DirectMessage) → Instant → State → HandlerResult × List Output
 pureHandler msg ts st
    with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = noChange , []
 ...| yes _
    with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = noChange , []
 ...| yes _
    with st ^∙ newValSender
 ...| nothing = (gotFirstAdvance (msg ^∙ author)) , []
 ...| just 1stSender
    with  (msg ^∙ author) ≟-PeerId 1stSender
 ...| yes refl = noChange , []
 ...| no  _    = (confirmedAdvance (msg ^∙ val))
                     , announce (msg ^∙ val)       -- Indicates agreement that we have reached this value
                     ∷ send (suc (msg ^∙ val)) ts  -- Initiates advance to next value
                     ∷ []

 handle : (msg : DirectMessage) → Instant → RWST Unit Output State Unit
 handle msg ts = do
   st ← get
   case proj₁ (pureHandler msg ts st) of
     λ { noChange             → pure unit
       ; (gotFirstAdvance  p) → newValSender ∙= just p
       ; (confirmedAdvance v) → do
           -- TODO: It's pretty weird to use the timestamp as a
           -- nondeterministic choice of recipient, but don't have any
           -- easy alternative currently
           maxSeen ∙= v
           newValSender ∙= nothing
       }
   tell (proj₂ (pureHandler msg ts st))

 handleDirect : DirectMessage → Instant → RWST Unit Output State Unit
 handleDirect msg ts
    with check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (fakePubKey (msg ^∙ author)) msg
 ...| nothing = pure unit
 ...| just ver = handle msg ts

 handleGossip : GossipMessage → Instant → RWST Unit Output State Unit
 handleGossip msg ts
    with check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (fakePubKey (msg ^∙ gmAuthor)) msg
 ...| nothing = pure unit  -- ACCOUNTABILITY OPPORTUNITY
 ...| just ver' = handleDirect (msg ^∙ original) ts

 stepPeer : (msg : Message) → Instant → State → State × List Output
 stepPeer (direct msg) ts st = proj₂ (RWST-run (handleDirect msg ts) unit st)
 stepPeer (gossip msg) ts st = proj₂ (RWST-run (handleGossip msg ts) unit st)

 unverifiedGossipNoEffect1 : ∀ {msg ts st}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (getPubKey (gossip msg)) msg ≡ nothing
   → stepPeer (gossip msg) ts st ≡ (st , [])
 unverifiedGossipNoEffect1 {msg} {ts} {st} prf rewrite prf = refl

 unverifiedGossipNoEffect2 : ∀ {msg ts st ver}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (getPubKey (gossip msg)) msg ≡ just ver
   → check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (getPubKey (direct (:original msg))) (:original msg) ≡ nothing
   → stepPeer (gossip msg) ts st ≡ (st , [])
 unverifiedGossipNoEffect2 {msg} {ts} {st} prf1 prf2 rewrite prf1 | prf2 = refl

 verifiedGossipEffect : ∀ {msg ts st ver ver'}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (getPubKey (gossip msg)) msg ≡ just ver
   → check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (getPubKey (direct (:original msg))) (:original msg) ≡ just ver'
   → stepPeer (gossip msg) ts st ≡ proj₂ (RWST-run (handleDirect (:original msg) ts) unit st)
 verifiedGossipEffect {msg} {ts} {st} prf1 prf2 rewrite prf1 | prf2 = refl

 ---------------------------------------------------------------------------
 -- Lemmas about the effects of steps, broken down by pureHandler results --
 ---------------------------------------------------------------------------

 nothingNoEffect : ∀ {ppre ppost m ts}
                 → proj₁ (pureHandler m ts ppre) ≡ noChange
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                 → ppre ≡ ppost
 nothingNoEffect {ppre} {m} {ts} {ppost} isNothing ppost≡ rewrite isNothing | ppost≡ = refl

 gFAEffect : ∀   {ppre ppost m ts sender}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                 → proj₁ (pureHandler m ts ppre) ≡ gotFirstAdvance sender
                 → :newValSender ppost ≡ just sender
                 × :maxSeen ppost ≡ :maxSeen ppre
 gFAEffect {ppre} {m} {ts} ppost≡ prf rewrite ppost≡ | prf = refl , refl

 cAEffect : ∀   {ppre ppost m ts newMax}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                 → proj₁ (pureHandler m ts ppre) ≡ confirmedAdvance newMax
                 → :newValSender ppost ≡ nothing
                 × :maxSeen      ppost ≡ newMax
 cAEffect {ppre} {ppost} {m} {ts} ppost≡ prf rewrite ppost≡ | prf = refl , refl


 ----------------------------------------------------------------------------------
 -- Lemmas about what the pureHandler result must be if certain variables change --
 ----------------------------------------------------------------------------------

 -- We can also include conclusions about the state change, which may be redundant with the
 -- "effects" lemmas above.  This redundancy allows for more convenient use of such conclusions when
 -- we are reasoning based on a state changes (such as in the "modifies*" lemmas below), while also
 -- allowing the conclusions to be used when breaking down cases my pattern matching on pureHandler
 -- results.  See demonstration of the two different approaches in the proof of rVWSRecvMsg below.

 modifiesMaxSeen : ∀ {ppre ppost m ts}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                 → ppre  ^∙ maxSeen ≢ ppost ^∙ maxSeen
                 → proj₁ (pureHandler m ts ppre) ≡ confirmedAdvance (ppost ^∙ maxSeen)
 modifiesMaxSeen {ppre} {ppost} {m} {ts} run≡ pre≢post rewrite run≡
    with proj₁ (pureHandler m ts ppre)
 ...| noChange            = ⊥-elim (pre≢post refl)
 ...| gotFirstAdvance p   = ⊥-elim (pre≢post refl)
 ...| confirmedAdvance v' = refl

 modifiesNewSenderVal : ∀ {ppre ppost m ts v}
                      → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                      → ppre  ^∙ newValSender ≢ ppost ^∙ newValSender
                      → ppost ^∙ newValSender ≡ just v
                      → proj₁ (pureHandler m ts ppre) ≡ gotFirstAdvance v
                      × ppost ^∙ maxSeen ≡ ppre ^∙ maxSeen
 modifiesNewSenderVal {ppre} {ppost} {m} {ts} {v} run≡ pre≢post jv rewrite run≡
    with proj₁ (pureHandler m ts ppre)
 ...| noChange            = ⊥-elim (pre≢post refl)
 ...| confirmedAdvance v' = ⊥-elim (maybe-⊥ jv refl)
 ...| gotFirstAdvance  v'
    with v' ≟ v
 ...| no neq   = ⊥-elim (neq (just-injective jv))
 ...| yes refl = refl , refl

 -----------------------------------------------------------------------------------
 -- Lemmas that capture what conditions must hold for various pureHandler results --
 -----------------------------------------------------------------------------------

 -- TO(NOT)DO: the structure of this mirrors pureHandler.  Maybe incorporate these proofs as Meta into
 -- pureHandler?  UPDATE: I started doing this, and realised it would be more trouble than it's worth
 -- (see branch mark-why-not-handler-contains-properties).
 gFACond : ∀ {st msg ts v}
         → proj₁ (pureHandler msg ts st) ≡ gotFirstAdvance v
         → :author msg ≡ v × :val msg ≡ suc (st ^∙ maxSeen)
 gFACond {st} {msg} {ts} {v} handler≡
    with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = ⊥-elim (nC≢gFA handler≡)
 ...| yes newMax
    with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = ⊥-elim (nC≢gFA handler≡)
 ...| yes newIsNext
    with st ^∙ newValSender
 ...| nothing = gFA-injective handler≡ , newIsNext
 ...| just 1stSender
    with  (msg ^∙ author) ≟-PeerId 1stSender
 ...| yes refl = ⊥-elim (nC≢gFA handler≡)
 ...| no _     = ⊥-elim (gFA≢cA (sym handler≡))


 cACond : ∀ {st msg ts v}
        → proj₁ (pureHandler msg ts st) ≡ confirmedAdvance v
        → :val msg ≡ v
        × v ≡ suc (st ^∙ maxSeen)
        × ∃[ p ] (st ^∙ newValSender ≡ just p × :author msg ≢ p)
 cACond {st} {msg} {ts} {v} handler≡
    with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = ⊥-elim (nC≢cA handler≡)
 ...| yes newMax
    with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = ⊥-elim (nC≢cA handler≡)
 ...| yes newIsNext
    with st ^∙ newValSender
 ...| nothing = ⊥-elim (gFA≢cA handler≡)
 ...| just 1stSender
    with (msg ^∙ author) ≟-PeerId 1stSender 
 ...| yes refl = ⊥-elim (nC≢cA handler≡ )
 ...| no diffSender
    with cA-injective handler≡
 ...| refl = refl , newIsNext , 1stSender , refl , diffSender

 -- Send actions cause messages to be sent, accounce actions do not
 exampleOutputsToSends : State → Output → List (PeerId × Message)
 exampleOutputsToSends s (announce _) = []
 exampleOutputsToSends s (send n peer) =  (peer , direct (mkDirectMessage (s ^∙ myId) n nothing)) ∷ []  -- TODO: sign message

 -- Our simple model is that there is a single fault.  For simplicity, I've assumed for now that
 -- it's peer 0, which is obviously not general enough, but enables progress on proofs.
 -- TODO: Use Meta to avoid "peeking"?
 dishonest : Message → Set
 dishonest m with getAuthor m ≟ 0
 ...| no _  = ⊥
 ...| yes d = ⊤

 -- Instantiate the SystemModel for our Example system
 open import LibraBFT.Global.SystemModel
               Instant
               PeerId
               _≟-PeerId_
               Message
               Output
               State
               canInit
               initialStateAndMessages
               stepPeer
               exampleOutputsToSends
               dishonest

 -- TODO: Somewhat of a DRY fail here.  Unify?
 verifySigDirect      : ∀ {pre post msg by ts}
                      → (P : SystemState → Set)
                      → (theStep : Step pre post)
                      → (iR : isRecvMsg theStep)
                      → P pre
                      → lookup by (peerStates pre) ≡ just (ppreOf iR)
                      → stepPeer (direct msg) ts (ppreOf iR) ≡ (ppostOf iR , actsOf iR)
                      → P post ⊎ ∃[ ver ] (check-signature (getPubKey (direct msg)) msg ≡ just ver)
 verifySigDirect {pre} {post} {msg} {by} {ts} P theStep iR Ppre rdy run≡
    with  check-signature (getPubKey (direct msg))  msg | inspect
         (check-signature (getPubKey (direct msg))) msg
 ...| just ver | [ R ] = inj₂ (ver , R)
 ...| nothing  | [ R ] rewrite R =
    inj₁ (InvariantStates≡ P
           (noChangePreservesState theStep iR (cong proj₁ (sym run≡)) (cong proj₂ (sym run≡)))
           Ppre)

 verifySigGossip      : ∀ {pre post msg by ts}
                      → (P : SystemState → Set)
                      → (theStep : Step pre post)
                      → (iR : isRecvMsg theStep)
                      → P pre
                      → lookup by (peerStates pre) ≡ just (ppreOf iR)
                      → stepPeer (gossip msg) ts (ppreOf iR) ≡ (ppostOf iR , actsOf iR)
                      → P post ⊎ ∃[ ver ] (check-signature (getPubKey (gossip msg)) msg ≡ just ver)
 verifySigGossip {pre} {post} {msg} {by} {ts} P theStep iR Ppre rdy run≡
    with  check-signature (getPubKey (gossip msg))  msg | inspect
         (check-signature (getPubKey (gossip msg))) msg
 ...| just ver | [ R ] = inj₂ (ver , R)
 ...| nothing  | [ R ] rewrite R =
    inj₁ (InvariantStates≡ P
           (noChangePreservesState theStep iR (cong proj₁ (sym run≡)) (cong proj₂ (sym run≡)))
           Ppre)

 -- The following (conceptually) easy invariant states that if peer p has recorded that p' sent the
 -- next value, then p' actually did sent it!

 -- Informal argument
 --
 -- If the action is an initPeer     for p (by ≡ p), then its initial state has nothing, contradicting second premise
 -- If the action is an initPeer not for p (by ≢ p), then p's peerState does not change, and the inductive hypothesis carries the day
 -- If the action is a cheat for any process, it does not modify anyone's peerStates, so inductive hypothesis carries the day again
 -- If the action is a recvMessage, it only *establishes* the condition if the message needed exists


 postulate
   mustBe : ∀ {p : PeerId}
          → {m1 : Message}
          → {m2 : DirectMessage}
          → {st : SystemState}
          → {pSt : State}
          → allegedlySent m1 st
          → lookup p (peerStates st) ≡ just pSt
          → (State → Message → WithVerSig m2)
          → allegedlySent (direct m2) st

 record RVWSConsequent (sender : PeerId) (curMax : ℕ) (st : SystemState) : Set where
   constructor mkRVWSConsequent
   field
     m     : DirectMessage
     sig   : WithVerSig m
     m∈SM  : allegedlySent (direct m) st
     auth≡ : m ^∙ author ≡ sender
     val≡  : m ^∙ val ≡ suc curMax
 open RVWSConsequent

 rVWSConsCast : ∀ {sender curMax pre post}
        → (preCons : RVWSConsequent sender curMax pre)
        → Step pre post
        → RVWSConsequent sender curMax post
 rVWSConsCast {pre = pre} {post = post} (mkRVWSConsequent m sig ∈SM-pre a v) theStep = mkRVWSConsequent m sig (cast∈SM {m} ∈SM-pre) a v
   where cast∈SM : ∀ {m'} → allegedlySent (direct m') pre → allegedlySent (direct m') post
         cast∈SM (inj₁ xx)      = inj₁ xx
         cast∈SM {m'} (inj₂ xx) = inj₂ (proj₁ xx , (msgs-stable {pre} {post} {proj₁ xx , direct m'} theStep (proj₂ xx)))

 RecordedValueWasSent : SystemState → Set
 RecordedValueWasSent st = ∀ {pSt curMax}
                           → (sender p : PeerId)
                           → lookup p (peerStates st) ≡ just pSt
                           → pSt ^∙ newValSender ≡ just sender
                           → pSt ^∙ maxSeen ≡ curMax
                           → RVWSConsequent sender curMax st

 rVWSInvariant : Invariant RecordedValueWasSent

 rVWSCheat : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → isCheatStep theStep
     → RecordedValueWasSent post
 rVWSCheat {pre} {post} preReach theStep isCheat {pSt} {curMax} sender p pSt≡ sender≡ max≡
   -- A cheat step does cannot "unsend" messages and does not affect anyone's state
   with rVWSInvariant preReach sender p (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep 
 
 rVWSInitPeer : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → isInitPeer theStep  -- Not needed in this example as it is trivial; keeping it to make example more general
     → RecordedValueWasSent post
 rVWSInitPeer {pre} {post} preReach theStep _ {pSt} sender p pSt≡ sender≡ max≡
   with peerOf theStep ≟ p
 ...| yes refl
   with theStep    -- TODO: Why can't I avoid this with clause by using rdyOf below?
                   -- It would simplify this proof by allowing this case to be in one line,
                   -- thus avoiding the need for spelling out the next case explicitly.
 ...| initPeer _ _ _ rdy
      -- After initializing p, the antecedent does not hold because :newValSender (lookup p (peerState post)) ≡ nothing
      = ⊥-elim (maybe-⊥ sender≡ (cong :newValSender (just-injective (trans (sym pSt≡) (lookup-correct rdy)))))

 rVWSInitPeer {pre} {post} preReach theStep _ {pSt} sender p pSt≡ sender≡ max≡
    | no xx
      -- Initializing "by" does not falsify the invariant for p ≢ by
   with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsg : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → isRecvMsg theStep
     → RecordedValueWasSent post
 rVWSRecvMsg {pre} {post} preReach
             theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv sender p pSt≡ sender≡ max≡
    with verifySigDirect {msg = msg} RecordedValueWasSent theStep isRecv (rVWSInvariant preReach) rdy run≡
 ...| inj₁ done = done sender p pSt≡ sender≡ max≡
 ...| inj₂ (ver , R)
    with peerOf theStep ≟ p
 ...| no xx
    -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
    with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsg {pre} {post} preReach
             theStep@(recvMsg {msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | inj₂ (ver , R)
    | yes refl

    -- Stash for later use: pSt ≡ ppost because of the "ready" condition for the step
    --                      definition of ppost
    with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡ | cong proj₁ run≡
 ...| pSt≡ppost | ppost≡
    -- The step is by p; consider cases of whether the antecedent holds in the prestate
    with Maybe-≡-dec _≟-PeerId_ (:newValSender ppre) (just sender) | curMax ≟ :maxSeen ppre
 ...| yes refl | yes refl
    -- It does, so the inductive hypothesis ensures the relevant message was sent before, and the step does not "unsend" it
    with rVWSInvariant preReach {pSt = ppre} sender p rdy refl refl
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsg {pre} {post} preReach
             (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | inj₂ (ver , R)
    | yes refl
    | pSt≡ppost | ppost≡
    | no nVSChanged | curMax≟maxSeen
    -- newValSender ≢ sender in the prestate. Because newValSender ≡ sender in the poststate, the handler
    -- result must be just (gotFirstAdvance sender)
    rewrite R
    with (sym pSt≡ppost) | (sym sender≡)
 ...| refl | refl
    with modifiesNewSenderVal {ppre} {ppost} {msg} {ts} {sender} (sym ppost≡) nVSChanged sender≡
 ...| handlerResult , maxSeenUnchanged  -- Here we use properties about the transition given by the modifies* lemma
    with curMax≟maxSeen                 -- In contrast, below we use the "effects" lemma separately.
    -- Again the relevant message was already sent (∈SM-pre), and the step does not unsend it.  From
    -- the condition required for this step, we can establish that the message has the required
    -- values.
 ...| no neq rewrite (sym pSt≡ppost) = ⊥-elim (neq (trans (sym max≡) maxSeenUnchanged))
 ...| yes refl
    with gFACond {ppre} {msg} {ts} handlerResult
 ...| auth≡ , val≡
    with ∈SM-pre
 ...| inj₁ dis =  mkRVWSConsequent msg ver (inj₁ dis) auth≡ val≡
 ...| inj₂ sentM = mkRVWSConsequent msg ver
                                       ((inj₂ (proj₁ sentM , (∈SM-stable-list
                                                               {actionsToSends ppost acts}
                                                               {sentMessages pre}
                                                               {proj₁ sentM , direct msg}
                                                               {! sentM !}))))   -- Victor please help, why won't it take sentM?
                                       auth≡ val≡
 rVWSRecvMsg {pre} {post} preReach
             (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | inj₂ (ver , R)
    | yes refl
    | pSt≡ppost | ppost≡
    | yes refl | no curMaxChanged
    rewrite R
    -- Because maxSeen changed, the handlerResult is a confirmedAdvance
    with (sym pSt≡ppost) | (sym max≡)
 ...| refl | refl
    with modifiesMaxSeen {ppre} {ppost} {msg} (sym ppost≡) (curMaxChanged ∘ sym)
 ...| isConfirmedAdvance
    -- Therefore, the step sets newValSender to nothing, thus ensuring that antecedent does not hold
    -- in the poststate
    -- Here we use the "effects" lemma, which is a little less convenient, but more general.  Keeping it
    -- this way for demonstration purposes.
    with cAEffect {ppre} {ppost} {msg} (sym ppost≡) isConfirmedAdvance
 ...| senderBecomesNothing , _ = ⊥-elim (maybe-⊥ sender≡ senderBecomesNothing)

 -- For gossip messages, we simply verify the signature and if it verifies, handle the original
 -- message it contains
 rVWSRecvMsg {pre} {post} preReach
             (recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv
             -- It's annoying that this case spells out all the parameters of rVWSInvariant just to then consumer them, but they are needed for the next case
    with verifySigGossip {msg = msg} RecordedValueWasSent (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv (rVWSInvariant preReach) rdy run≡
 ...| inj₁ done = done
 ...| inj₂ (ver' , R') rewrite R'
    -- This is somewhat redundant with verifySig*, but couldn't quite use it.  TODO: try again, think about unverifiedgossipnoeffect2
    with check-signature (getPubKey (direct (:original msg)))  (:original msg) | inspect
        (check-signature (getPubKey (direct (:original msg)))) (:original msg)
 ...| nothing | [ R'' ]
              = (InvariantStates≡
                  RecordedValueWasSent
                  (noChangePreservesState
                    (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy (trans (unverifiedGossipNoEffect2 R' R'') run≡))
                    isRecv
                    (cong proj₁ (sym run≡))
                    (cong proj₂ (sym run≡)))
                  (rVWSInvariant preReach))

 rVWSRecvMsg {pre} {post} preReach
             (recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv
    | inj₂ (ver' , R')
    | (just ver'') | [ R'' ] rewrite R'
    with mustBe {m1 = gossip msg} {m2 = :original msg} {pre} {ppre} ∈SM-pre rdy (λ _ _ → ver'')
 ...| xx
    with verifiedGossipEffect {msg} {ts} {ppre} {ver'} {ver''} R' R''
 ...| xxy rewrite R' | R'' = rVWSRecvMsg {pre} {post} preReach                 -- TODO: revisit after deciding about "to" parameter
                                         (recvMsg {pre} {direct (:original msg)} {ppre = ppre} {ppost = ppost} {acts} by ts xx rdy {! xxy!} ) tt
                               -- Victor please help.  Why can't I get it to recognise that the
                               -- signature check on ":original msg" has succeeded (R'' say it has,
                               -- but the error if I try to give xxy for the hole suggests it
                               -- hasn't, despite the rewriting of R'')

 rVWSInvariant init sender p x = ⊥-elim (maybe-⊥ x kvm-empty)
 rVWSInvariant (step preReach (cheat by ts to m dis))  = rVWSCheat preReach (cheat by ts to m dis) tt
 rVWSInvariant (step preReach (initPeer by ts cI rdy)) = rVWSInitPeer preReach (initPeer by ts cI rdy) tt
 rVWSInvariant (step preReach (recvMsg by ts ∈SM-pre ready trans)) = rVWSRecvMsg preReach (recvMsg by ts ∈SM-pre ready trans) tt

--  -- Another way of approaching the proof is to do case analysis on pureHandler results.
--  -- In this example, if proj₁ (pureHandler msg ts ppre) =
--  --   nothing              -- then the antecedent holds in the prestate, so the inductive hypothesis and ∈SM-stable-list suffice
--  --   confirmedAdvance _   -- then the effect is to set newValSender to nothing, ensuring the antecedent does not hold
--  --   gotFirstAdvance  p'  -- requires case analysis on whether p' ≡ p and maxSeen ppre and the message contents
--  rVWSInvariant2 : Invariant RecordedValueWasSent


--  {-# TERMINATING #-} -- MSM: Why is this necessary?  See comment on other TERMINATING directive above.

--  rVWSRecvMsg2 : ∀ {pre post}
--      → ReachableSystemState pre
--      → (theStep : Step pre post)
--      → isRecvMsg theStep
--      → RecordedValueWasSent post

--  rVWSRecvMsg2 {pre} {post} preReach
--               theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
--     with verifySigDirect {msg = msg} RecordedValueWasSent theStep isRecv (rVWSInvariant preReach) rdy run≡
--  ...| inj₁ done = done sender p pSt≡ sender≡ max≡
--  ...| inj₂ (ver , R)
--     with peerOf theStep ≟ p
--  ...| no xx
--     -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
--     with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
--  ...| preCons = rVWSConsCast preCons (msgs-stable theStep (m∈SM preCons))

--  rVWSRecvMsg2 {pre} {post} preReach
--              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
--     | inj₂ (ver , R)
--     | yes refl
--     rewrite R
--     with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡
--  ...| pSt≡ppost
--     with cong proj₁ (sym run≡)
--  ...| ppost≡
--     with proj₁ (pureHandler msg ts ppre) ≟HR noChange
--  ...| yes hR≡noChange
--     with nothingNoEffect {ppre} {ppost} {msg} {ts} hR≡noChange ppost≡
--  ...| noEffect
--     with pSt≡ppost | sym noEffect
--  ...| refl | refl
--     with rVWSInvariant preReach {pSt = ppre} sender p rdy sender≡ max≡
--  ...| preCons = rVWSConsCast preCons (∈SM-stable-list {msgs = actionsToSends ppre acts} (m∈SM preCons))   -- TODO: simplify using system model function/

--  rVWSRecvMsg2 {pre} {post} preReach
--              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
--     | inj₂ (ver , R)
--     | yes refl
--     | pSt≡ppost
--     | ppost≡
--     | no hR≢noChange
--     rewrite R
--     with isGotFirstAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
--          isGotFirstAdvance (proj₁ (pureHandler msg ts ppre))
--  ...| just n | [ hR≡gFA ]
--     with gFAEffect {ppre} {ppost} {msg} {ts} {n} ppost≡ (isGotFirstAdvance≡ hR≡gFA)
--  ...| senderBecomesN , maxUnchanged
--     with pSt≡ppost | n ≟-PeerId sender
--  ...| refl | no n≢sender = ⊥-elim (n≢sender (just-injective (trans (sym senderBecomesN) sender≡)))
--  ...| refl | yes refl
--     with (sym pSt≡ppost) | curMax ≟ :maxSeen ppre
--  ...| refl | no xx = ⊥-elim (xx (trans (sym max≡) maxUnchanged))
--  ...| refl | yes refl
--     with gFACond {ppre} {msg} {ts} {n} (isGotFirstAdvance≡ {proj₁ (pureHandler msg ts ppre)} {n} hR≡gFA)
--  ...| auth≡ , val≡ = mkRVWSConsequent to msg ver
--                           (∈SM-stable-list {actionsToSends ppost acts} ∈SM-pre)
--                           auth≡ val≡

--  rVWSRecvMsg2 {pre} {post} preReach
--              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
--     | inj₂ (ver , R)
--     | yes refl
--     | pSt≡ppost
--     | ppost≡
--     | no hR≢noChange
--     | nothing | [ hR≢gFA ]
--     rewrite R
--     with isConfirmedAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
--          isConfirmedAdvance (proj₁ (pureHandler msg ts ppre))
--  ...| nothing | [ hR≢cA ] = ⊥-elim (hR≢noChange (handlerResultIsSomething {proj₁ (pureHandler msg ts ppre)} hR≢cA hR≢gFA))
--  ...| just n' | [ hR≡cA ]
--     with  pSt≡ppost | cAEffect {ppre} {ppost} {msg} {ts} ppost≡ (isConfirmedAdvance≡ hR≡cA)
--  ...| refl | senderBecomesNothing , _ = ⊥-elim (maybe-⊥ sender≡ senderBecomesNothing)

--  -- For gossip messages, we simply verify the signature and if it verifies, handle the original
--  -- message it contains
--  rVWSRecvMsg2 {pre} {post} preReach
--              theStep@(recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv
--     with verifySigGossip {msg = msg} RecordedValueWasSent theStep isRecv (rVWSInvariant preReach) rdy run≡
--  ...| inj₁ done = done
--  ...| inj₂ (ver' , R') = rVWSRecvMsg2 {pre} {post} preReach theStep isRecv

--  rVWSInvariant2 init sender p x = ⊥-elim (maybe-⊥ x kvm-empty)
--  rVWSInvariant2 (step preReach (cheat by ts to m dis))  = rVWSCheat preReach (cheat by ts to m dis) tt
--  rVWSInvariant2 (step preReach (initPeer by ts cI rdy)) = rVWSInitPeer preReach (initPeer by ts cI rdy) tt
--  rVWSInvariant2 (step preReach (recvMsg by ts ∈SM-pre ready trans)) = rVWSRecvMsg2 preReach (recvMsg by ts ∈SM-pre ready trans) tt

--  -----------------------------------------------------------------------------------------

-- --  record CVSB2Consequent (sender1 sender2 : PeerId) (curMax : ℕ) (st : SystemState) : Set where
-- --    constructor mkCVSB2Consequent
-- --    field
-- --      senders≢ : sender2 ≢ sender1
-- --      msg1     : RVWSConsequent sender1 curMax st
-- --      msg2     : RVWSConsequent sender2 curMax st
-- --  open CVSB2Consequent

-- --  cVSB2ConsCast : ∀ {sender1 sender2 curMax pre post}
-- --                → (preCons : CVSB2Consequent sender1 sender2 curMax pre)
-- --                → (to (msg1 preCons) , direct (m (msg1 preCons))) ∈SM (sentMessages post)
-- --                → (to (msg2 preCons) , direct (m (msg2 preCons))) ∈SM (sentMessages post)
-- --                → CVSB2Consequent sender1 sender2 curMax post
-- --  cVSB2ConsCast (mkCVSB2Consequent senders≢ xx1 xx2) ∈SM1-post ∈SM2-post =
-- --                 mkCVSB2Consequent
-- --                   senders≢
-- --                   (rVWSConsCast xx1 ∈SM1-post)
-- --                   (rVWSConsCast xx2 ∈SM2-post)

-- --  -- If an honest peer has recorded the maximum value seen as suc curMax,
-- --  -- then two different peers have sent messages with value curMax
-- --  CommittedValueWasSentBy2 : SystemState → Set
-- --  CommittedValueWasSentBy2 st = ∀ {pSt curMax p}
-- --                           → lookup p (peerStates st) ≡ just pSt
-- --                           → pSt ^∙ maxSeen ≡ suc curMax
-- --                           → ∃[ sender1 ] ∃[ sender2 ] (CVSB2Consequent sender1 sender2 curMax st)

-- --  cVSB2Invariant : Invariant CommittedValueWasSentBy2

-- --  cVSB2Cheat : ∀ {pre post}
-- --      → ReachableSystemState pre
-- --      → (theStep : Step pre post)
-- --      → isCheatStep theStep
-- --      → CommittedValueWasSentBy2 post
-- --  cVSB2Cheat preReach theStep isCheat {pSt} {curMax} {p} pSt≡ max≡
-- --    -- A cheat step does cannot "unsend" messages and does not affect anyone's state
-- --    with cVSB2Invariant preReach (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) max≡
-- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- --  cVSB2InitPeer : ∀ {pre post}
-- --      → ReachableSystemState pre
-- --      → (theStep : Step pre post)
-- --      → isInitPeer theStep
-- --      → CommittedValueWasSentBy2 post
-- --  cVSB2InitPeer {pre} {post} preReach theStep _ {pSt} {curMax} {p} pSt≡ max≡
-- --    with peerOf theStep ≟ p
-- --  ...| yes refl
-- --    with theStep
-- --  ...| initPeer _ _ _ rdy
-- --       -- After initializing p, the antecedent does not hold because :curMax ≡ 0
-- --    with just-injective (trans (sym pSt≡) (lookup-correct rdy))
-- --  ...| xxx
-- --       = ⊥-elim (1+n≢0 {curMax} (trans (sym max≡) (cong :maxSeen xxx)))

-- --  cVSB2InitPeer {pre} {post} preReach theStep _ {pSt} {curMax} {p} pSt≡ max≡
-- --     | no xx
-- --       -- Initializing "by" does not falsify the invariant for p ≢ by
-- --    with cVSB2Invariant preReach (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) max≡
-- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- --  {-# TERMINATING #-} -- MSM: Why is this necessary?  See comment on other TERMINATING directive above.
-- --  cVSB2RecvMsg : ∀ {pre post}
-- --      → ReachableSystemState pre
-- --      → (theStep : Step pre post)
-- --      → isRecvMsg theStep
-- --      → CommittedValueWasSentBy2 post

-- --  cVSB2RecvMsg {pre} {post} preReach
-- --               theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- --     with verifySigDirect {msg = msg} CommittedValueWasSentBy2 theStep isRecv (cVSB2Invariant preReach) rdy run≡
-- --  ...| inj₁ done = done pSt≡ max≡
-- --  ...| inj₂ (ver , R)
-- --     with peerOf theStep ≟ p
-- --  ...| no xx
-- --     -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
-- --     with cVSB2Invariant preReach (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) max≡
-- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- --  cVSB2RecvMsg {pre} {post} preReach
-- --                        (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- --     | inj₂ (ver , R)
-- --     | yes refl
-- --     rewrite R
-- --     with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡
-- --  ...| pSt≡ppost
-- -- --    with cong proj₁ run≡ | cong proj₂ (sym run≡)
-- --     with cong proj₁ (sym run≡) | cong proj₂ (sym run≡)
-- --  ...| ppost≡ | acts≡
-- --     with proj₁ (pureHandler msg ts ppre) ≟HR noChange
-- --  ...| yes hR≡noChange
-- --     with nothingNoEffect {ppre} {ppost} {msg} {ts} hR≡noChange ppost≡
-- --  ...| noEffect
-- --     with pSt≡ppost | sym noEffect
-- --  ...| refl | refl
-- --     with cVSB2Invariant preReach {pSt = ppre} {p = p} rdy max≡
-- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (∈SM-stable-list {msgs = actionsToSends ppre acts} (m∈SM (msg1 preCons)))
-- --                                                           (∈SM-stable-list {msgs = actionsToSends ppre acts} (m∈SM (msg2 preCons)))

-- --  cVSB2RecvMsg {pre} {post} preReach
-- --              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- --     | inj₂ (ver , R)
-- --     | yes refl
-- --     | pSt≡ppost
-- --     | ppost≡ | acts≡
-- --     | no hR≢noChange
-- --     rewrite R
-- --     with isGotFirstAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
-- --          isGotFirstAdvance (proj₁ (pureHandler msg ts ppre))
-- --  ...| just n | [ hR≡gFA ]
-- --     with gFAEffect {ppre} {ppost} {msg} {ts} {n} ppost≡ (isGotFirstAdvance≡ hR≡gFA)
-- --  ...| senderBecomesN , maxUnchanged
-- --     with (sym pSt≡ppost) | suc curMax ≟ :maxSeen ppre
-- --  ...| refl | no xx = ⊥-elim (xx (trans (sym max≡) maxUnchanged))
-- --  ...| refl | yes refl
-- --     with max≡
-- --  ...| refl
-- --     with cVSB2Invariant preReach {pSt = ppre} {p = p} rdy refl
-- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (∈SM-stable-list {actionsToSends ppost acts} (m∈SM (msg1 preCons)))
-- --                                                           (∈SM-stable-list {actionsToSends ppost acts} (m∈SM (msg2 preCons)))
-- --  cVSB2RecvMsg {pre} {post} preReach
-- --              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- --     | inj₂ (ver , R)
-- --     | yes refl
-- --     | pSt≡ppost
-- --     | ppost≡ | acts≡
-- --     | no hR≢noChange
-- --     | nothing | [ hR≢gFA ]
-- --     rewrite R
-- --     with isConfirmedAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
-- --          isConfirmedAdvance (proj₁ (pureHandler msg ts ppre))
-- --  ...| nothing | [ hR≢cA ] = ⊥-elim (hR≢noChange (handlerResultIsSomething {proj₁ (pureHandler msg ts ppre)} hR≢cA hR≢gFA))
-- --  ...| just v' | [ hR≡cA ]
-- --     with  pSt≡ppost | cAEffect {ppre} {ppost} {msg} {ts} ppost≡ (isConfirmedAdvance≡ hR≡cA)
-- --  ...| refl | senderBecomesNothing , maxNew
-- --     with cACond {ppre} {msg} {ts} {v = v'} (isConfirmedAdvance≡ hR≡cA)
-- --  ...| msgVal≡v' , zzz , sender1 , xxx , diffSender
-- --     with :val msg ≟ v'
-- --  ...| no neq   = ⊥-elim (neq msgVal≡v')
-- --  ...| yes refl
-- --     with rVWSInvariant preReach {pSt = ppre} {curMax = :maxSeen ppre} sender1 p rdy xxx refl
-- --  ...| s1preCon
-- --     with suc-injective (trans (sym max≡) (trans maxNew zzz))
-- --  ...| refl = sender1
-- --            , :author msg
-- --            , (mkCVSB2Consequent
-- --                 diffSender
-- --                 (rVWSConsCast s1preCon (∈SM-stable-list {actionsToSends ppost acts} (m∈SM s1preCon)))
-- --                 (mkRVWSConsequent to msg ver
-- --                    (∈SM-stable-list {actionsToSends ppost acts } ∈SM-pre)
-- --                    refl
-- --                    (trans (sym maxNew) max≡)))

-- --  cVSB2RecvMsg {pre} {post} preReach
-- --               theStep@(recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv
-- --     with verifySigGossip {msg = msg} CommittedValueWasSentBy2 theStep isRecv (cVSB2Invariant preReach) rdy run≡
-- --  ...| inj₁ done = done
-- --  ...| inj₂ (ver' , R') = cVSB2RecvMsg {pre} {post} preReach theStep isRecv

-- --  cVSB2Invariant init {p = p} x = ⊥-elim (maybe-⊥ x kvm-empty)
-- --  cVSB2Invariant (step preReach (cheat by ts to m dis))  = cVSB2Cheat preReach (cheat by ts to m dis) tt
-- --  cVSB2Invariant (step preReach (initPeer by ts cI rdy)) = cVSB2InitPeer preReach (initPeer by ts cI rdy) tt
-- --  cVSB2Invariant (step preReach (recvMsg by ts ∈SM-pre ready trans)) = cVSB2RecvMsg preReach (recvMsg by ts ∈SM-pre ready trans) tt
