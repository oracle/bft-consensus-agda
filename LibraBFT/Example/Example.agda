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

 _≟-PeerId_ : (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
 _≟-PeerId_ = _≟_

 record Message : Set where
   constructor mkMessage
   field
     :author : PeerId
     :val    : ℕ
     :sigMB  : Maybe Signature
 open Message

 unquoteDecl author   val   sigMB = mkLens (quote Message)
            (author ∷ val ∷ sigMB ∷ [])

 data Action : Set where
   announce : ℕ → Action           -- This is analogous to "commit"
   send     : ℕ → PeerId → Action


 instance
   sig-Message : WithSig Message
   sig-Message = record
      { Signed         = Is-just ∘ :sigMB
      ; isSigned?      = λ m → Maybe-Any-dec (λ _ → yes tt) (m ^∙ sigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ m → concat ( encode  (m ^∙ author)
                                      ∷ encode  (m ^∙ val)
                                      ∷ [])
      }

 record State : Set where
   constructor mkState
   field
     :myId         : PeerId
     :maxSeen      : ℕ
     :newValSender : Maybe PeerId
 open State

 unquoteDecl myId   maxSeen   newValSender = mkLens (quote State)
            (myId ∷ maxSeen ∷ newValSender ∷ [])

 canInit : PeerId → Set
 canInit p = ⊤

 initialStateAndMessages : (p : PeerId) → canInit p → State × List Action
 initialStateAndMessages p _ = mkState p 0 nothing , []  -- TODO : send something!

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

 handlerResultConstructorDiff : ∀ {p n} → gotFirstAdvance p ≢ confirmedAdvance n
 handlerResultConstructorDiff ()

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
 pureHandler : Message → Instant → State → HandlerResult × List Action
 pureHandler msg ts st
    with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = noChange , []
 ...| yes _
    with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = noChange , []
 ...| yes _
    with st ^∙ newValSender
 ...| nothing = (gotFirstAdvance (msg ^∙ author)) , []
 ...| just 1stSender = (confirmedAdvance (msg ^∙ val))
                     , announce (msg ^∙ val)       -- Indicates agreement that we have reached this value
                     ∷ send (suc (msg ^∙ val)) ts  -- Initiates advance to next value
                     ∷ []

 handle : Message → Instant → RWST Unit Action State Unit
 handle msg ts = do  -- TODO: Check signature
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

 ---------------------------------------------------------------------------
 -- Lemmas about the effects of steps, broken down by pureHandler results --
 ---------------------------------------------------------------------------

 nothingNoEffect : ∀ {ppre  ppost m ts env}
                 → proj₁ (pureHandler m ts ppre) ≡ noChange
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) env ppre)
                 → ppre ≡ ppost
 nothingNoEffect {ppre} {m} {ts} {env} {ppost} isNothing ppost≡ rewrite isNothing | ppost≡ = refl

 gFAEffect : ∀   {ppre ppost m ts env sender}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) env ppre)
                 → proj₁ (pureHandler m ts ppre) ≡ gotFirstAdvance sender
                 → :newValSender ppost ≡ just sender
                 × :maxSeen ppost ≡ :maxSeen ppre
 gFAEffect {ppre} {m} {ts} {env} ppost≡ prf rewrite ppost≡ | prf = refl , refl

 cAEffect : ∀   {ppre ppost m ts env newMax}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) env ppre)
                 → proj₁ (pureHandler m ts ppre) ≡ confirmedAdvance newMax
                 → :newValSender ppost ≡ nothing
                 × :maxSeen      ppost ≡ newMax
 cAEffect {ppre} {ppost} {m} {ts} {env} ppost≡ prf rewrite ppost≡ | prf = refl , refl


 ----------------------------------------------------------------------------------
 -- Lemmas about what the pureHandler result must be if certain variables change --
 ----------------------------------------------------------------------------------

 -- We can also include conclusions about the state change, which may be redundant with the
 -- "effects" lemmas above.  This redundancy allows for more convenient use of such conclusions when
 -- we are reasoning based on a state changes (such as in the "modifies*" lemmas below), while also
 -- allowing the conclusions to be used when breaking down cases my pattern matching on pureHandler
 -- results.  See demonstration of the two different approaches in the proof of rVWSRecvMsg below.

 modifiesMaxSeen : ∀ {ppre ppost m ts env}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) env ppre)
                 → ppre  ^∙ maxSeen ≢ ppost ^∙ maxSeen
                 → proj₁ (pureHandler m ts ppre) ≡ confirmedAdvance (ppost ^∙ maxSeen)
 modifiesMaxSeen {ppre} {ppost} {m} {ts} {env} run≡ pre≢post rewrite run≡
    with proj₁ (pureHandler m ts ppre)
 ...| noChange            = ⊥-elim (pre≢post refl)
 ...| gotFirstAdvance p   = ⊥-elim (pre≢post refl)
 ...| confirmedAdvance v' = refl

 modifiesNewSenderVal : ∀ {ppre ppost m ts env v}
                      → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) env ppre)
                      → ppre  ^∙ newValSender ≢ ppost ^∙ newValSender
                      → ppost ^∙ newValSender ≡ just v
                      → proj₁ (pureHandler m ts ppre) ≡ gotFirstAdvance v
                      × ppost ^∙ maxSeen ≡ ppre ^∙ maxSeen
 modifiesNewSenderVal {ppre} {ppost} {m} {ts} {env} {v} run≡ pre≢post jv rewrite run≡
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

 -- TODO: the structure of this mirrors pureHandler.  Maybe incorporate these proofs as Meta into
 -- pureHandler?
 modifiesNewSenderValCond : ∀ {st msg ts v}
                          → proj₁ (pureHandler msg ts st) ≡ gotFirstAdvance v
                          → :author msg ≡ v × :val msg ≡ suc (st ^∙ maxSeen)
 modifiesNewSenderValCond {st} {msg} {ts} {v} handler≡
    with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = ((λ ()) handler≡) -- TODO: How to avoid these warnings?  Need trivial auxiliary lemma?
 ...| yes newMax
    with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = ((λ ()) handler≡)
 ...| yes newIsNext
    with st ^∙ newValSender
 ...| nothing = gFA-injective handler≡ , newIsNext
 ...| just 1stSender = (((λ ()) handler≡))


 -- Send actions cause messages to be sent, accounce actions do not
 exampleActionsToSends : State → Action → List (PeerId × Message)
 exampleActionsToSends s (announce _) = []
 exampleActionsToSends s (send n peer) =  (peer , (mkMessage (s ^∙ myId) n nothing)) ∷ []  -- TODO: sign message

 -- Our simple model is that there is a single fault.  For simplicity, I've assumed for now that
 -- it's peer 0, which is obviously not general enough, but enables progress on proofs.
 -- TODO: Use Meta to avoid "peeking"?
 dishonest : Message → PeerId → Set
 dishonest m peer with peer ≟ 0
 ...| no _  = ⊥
 ...| yes d = ⊤

 -- Instantiate the SystemModel for our Example system
 open import LibraBFT.Global.SystemModel
               Instant
               PeerId
               _≟-PeerId_
               Message
               sig-Message
               Unit
               Action
               State
               canInit
               initialStateAndMessages
               handle
               exampleActionsToSends
               dishonest

 -- The following (conceptually) easy invariant states that if peer p has recorded that p' sent the
 -- next value, then p' actually did sent it!

 -- Informal argument
 --
 -- If the action is an initPeer     for p (by ≡ p), then its initial state has nothing, contradicting second premise
 -- If the action is an initPeer not for p (by ≢ p), then p's peerState does not change, and the inductive hypothesis carries the day
 -- If the action is a cheat for any process, it does not modify anyone's peerStates, so inductive hypothesis carries the day again
 -- If the action is a recvMessage, it only *establishes* the condition if the message needed exists

 recordedValueWasSent : SystemState → Set
 recordedValueWasSent st = ∀ {pSt curMax}
                           → (sender p : PeerId)
                           → lookup p (peerStates st) ≡ just pSt
                           → pSt ^∙ newValSender ≡ just sender
                           → pSt ^∙ maxSeen ≡ curMax
                           → Σ PeerId λ recip → Σ Message (λ msg → WithVerSig msg
                                                                 × (recip , msg) ∈SM sentMessages st
                                                                 × msg ^∙ author ≡ sender
                                                                 × msg ^∙ val ≡ suc curMax)

 rVWSInvariant : Invariant recordedValueWasSent

 rVWSCheat : ∀ {pre post by ts}
     → ReachableSystemState pre
     → (theStep : Step by pre ts post)
     → isCheatStep theStep
     → recordedValueWasSent post
 rVWSCheat preReach theStep isCheat {pSt} sender p pSt≡ sender≡ max≡
   -- A cheat step does cannot "unsend" messages and does not affect anyone's state
   with rVWSInvariant preReach sender p (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) sender≡ max≡
   -- TODO: it would be nice to have a succinct "map function over nth element of tuple", but doing
   --       this in a type-generic way is tricky.  Maybe just do specific functions for fixed-sized
   --       tuples?  Even that is tricky to do in a general way when the function to map over one
   --       component (msg-stable theStep in thie case) has implicit arguments.
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSInitPeer : ∀ {pre post by ts}
     → ReachableSystemState pre
     → (theStep : Step by pre ts post)
     → isInitPeer theStep
     → recordedValueWasSent post
 rVWSInitPeer {pre} {post} {by} {ts} preReach theStep isInit {pSt} sender p pSt≡ sender≡ max≡
   with by ≟ p
 ...| yes refl
   with theStep    -- TODO: Why can't I avoid this with clause by using rdyOf below?
                   -- It would simplify this proof by allowing this case to be in one line,
                   -- thus avoiding the need for spelling out the next case explicitly.
 ...| initPeer _ _ rdy
      -- After initializing p, the antecedent does not hold because :newValSender (lookup p (peerState post)) ≡ nothing
      = ⊥-elim (maybe-⊥ sender≡ (cong :newValSender (just-injective (trans (sym pSt≡) (lookup-correct rdy)))))
 rVWSInitPeer {pre} {post} {by} {ts} preReach theStep isInit {pSt} sender p pSt≡ sender≡ max≡
    | no xx
      -- Initializing "by" does not falsify the invariant for p ≢ by
   with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSRecvMsg : ∀ {pre post by ts}
     → ReachableSystemState pre
     → (theStep : Step by pre ts post)
     → isRecvMsg theStep
     → recordedValueWasSent post
 rVWSRecvMsg {pre} {post} {by} {ts} preReach theStep isInit {pSt} sender p pSt≡ sender≡ max≡
    with by ≟ p
 ...| no xx
    -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
    with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSRecvMsg {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    -- Stash for later use: pSt ≡ ppost because of the "ready" condition for the step
    --                      definition of ppost
    with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡ | cong proj₁ (cong proj₂ run≡)
 ...| pSt≡ppost | ppost≡
    -- The step is by p; consider cases of whether the antecedent holds in the prestate
    with Maybe-≡-dec _≟-PeerId_ (:newValSender ppre) (just sender) | curMax ≟ :maxSeen ppre
 ...| yes refl | yes refl
    -- It does, so the inductive hypothesis ensures the relevant message was sent before, and the step does not "unsend" it
    with rVWSInvariant preReach {pSt = ppre} sender p rdy refl refl
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSRecvMsg {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    | pSt≡ppost | ppost≡
    | no nVSChanged | curMax≟maxSeen
    -- newValSender ≢ sender in the prestate. Because newValSender ≡ sender in the poststate, the handler
    -- result must be just (gotFirstAdvance sender)
    with (sym pSt≡ppost) | (sym sender≡)
 ...| refl | refl
    with modifiesNewSenderVal {ppre} {ppost} {msg} {ts} {env} {sender} (sym ppost≡) nVSChanged sender≡
 ...| handlerResult , maxSeenUnchanged  -- Here we use properties about the transition given by the modifies* lemma
    with curMax≟maxSeen                 -- In contrast, below we use the "effects" lemma separately.
    -- Again the relevant message was already sent (∈SM-pre), and the step does not unsend it.  From
    -- the condition required for this step, we can establish that the message has the required
    -- values.
 ...| yes refl = to
                , msg
                , {!!}
                , ∈SM-stable-list {sentMessages pre} {to , msg} {actionsToSends ppost acts} ∈SM-pre
                , modifiesNewSenderValCond {ppre} {msg} {ts} handlerResult
 ...| no neq rewrite (sym pSt≡ppost) = ⊥-elim (neq (trans (sym max≡) maxSeenUnchanged))

 rVWSRecvMsg {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    | pSt≡ppost | ppost≡
    | yes refl | no curMaxChanged
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

 -- TODO: so far, we have not modeled signature verification.  This should
 -- be done systematically by the system being modeled.  We should not make
 -- the SystemModel ensure messages received have their signature verified.
 -- A question is where the public key is, and how this is derived from the
 -- received message.

 rVWSInvariant init sender p x = ⊥-elim (maybe-⊥ x kvm-empty)
 rVWSInvariant (step preReach (cheat ts to m dis))  = rVWSCheat preReach (cheat ts to m dis) tt
 rVWSInvariant (step preReach (initPeer ts cI rdy)) = rVWSInitPeer preReach (initPeer ts cI rdy) tt
 rVWSInvariant (step preReach (recvMsg ts ∈SM-pre ready trans)) = rVWSRecvMsg preReach (recvMsg ts ∈SM-pre ready trans) tt 


 -- Another way of approaching the proof is to do case analysis on pureHandler results.
 -- In this example, if proj₁ (pureHandler msg ts ppre) =
 --   nothing              -- then the antecedent holds in the prestate, so the inductive hypothesis and ∈SM-stable-list suffice
 --   confirmedAdvance _   -- then the effect is to set newValSender to nothing, ensuring the antecedent does not hold
 --   gotFirstAdvance  p'  -- requires case analysis on whether p' ≡ p and maxSeen ppre and the message contents
 rVWSInvariant2 : Invariant recordedValueWasSent

 rVWSRecvMsg2 : ∀ {pre post by ts}
     → ReachableSystemState pre
     → (theStep : Step by pre ts post)
     → isRecvMsg theStep
     → recordedValueWasSent post
 rVWSRecvMsg2 {pre} {post} {by} {ts} preReach theStep isInit {pSt} sender p pSt≡ sender≡ max≡
    with by ≟ p
 ...| no xx
    -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
    with rVWSInvariant preReach sender p (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSRecvMsg2 {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡
 ...| pSt≡ppost
    with cong (proj₁ ∘ proj₂) (sym run≡)
 ...| ppost≡
    with proj₁ (pureHandler msg ts ppre) ≟HR noChange
 ...| yes hR≡noChange
    with nothingNoEffect {ppre} {ppost} {msg} {ts} {env} hR≡noChange ppost≡
 ...| noEffect
    with pSt≡ppost | sym noEffect
 ...| refl | refl
    with rVWSInvariant preReach {pSt = ppre} sender p rdy sender≡ max≡
 ...| xx1 , xx2 , xx3 , xx4 , xx5 = xx1 , xx2 , xx3 , msgs-stable theStep xx4 , xx5

 rVWSRecvMsg2 {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    | pSt≡ppost
    | ppost≡
    | no hR≢noChange
    with isGotFirstAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
         isGotFirstAdvance (proj₁ (pureHandler msg ts ppre))
 ...| just n | [ hR≡gFA ]
    with gFAEffect {ppre} {ppost} {msg} {ts} {env} {n} ppost≡ (isGotFirstAdvance≡ hR≡gFA)
 ...| senderBecomesN , maxUnchanged
    with pSt≡ppost | n ≟-PeerId sender
 ...| refl | no n≢sender = ⊥-elim (n≢sender (just-injective (trans (sym senderBecomesN) sender≡)))
 ...| refl | yes refl
    with (sym pSt≡ppost) | curMax ≟ :maxSeen ppre
 ...| refl | no xx = ⊥-elim (xx (trans (sym max≡) maxUnchanged))
 ...| refl | yes refl = to , msg , {!!}, (∈SM-stable-list {sentMessages pre} {to , msg} {actionsToSends ppost acts} ∈SM-pre)
                                 , modifiesNewSenderValCond {ppre} {msg} {ts} {n} (isGotFirstAdvance≡ {proj₁ (pureHandler msg ts ppre)} {n} hR≡gFA)

 rVWSRecvMsg2 {pre} {post} {by} {ts} preReach
             theStep@(recvMsg {msg} {to} {env} {ppre} {ppost} {acts} .ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} sender p pSt≡ sender≡ max≡
    | yes refl
    | pSt≡ppost
    | ppost≡
    | no hR≢noChange
    | nothing | [ hR≢gFA ]
    with isConfirmedAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
         isConfirmedAdvance (proj₁ (pureHandler msg ts ppre))
 ...| nothing | [ hR≢cA ] = ⊥-elim (hR≢noChange (handlerResultIsSomething {proj₁ (pureHandler msg ts ppre)} hR≢cA hR≢gFA))
 ...| just n' | [ hR≡cA ]
    with  pSt≡ppost | cAEffect {ppre} {ppost} {msg} {ts} {env} ppost≡ (isConfirmedAdvance≡ hR≡cA)
 ...| refl | senderBecomesNothing , _ = ⊥-elim (maybe-⊥ sender≡ senderBecomesNothing)

 rVWSInvariant2 init sender p x = ⊥-elim (maybe-⊥ x kvm-empty)
 rVWSInvariant2 (step preReach (cheat ts to m dis))  = rVWSCheat preReach (cheat ts to m dis) tt
 rVWSInvariant2 (step preReach (initPeer ts cI rdy)) = rVWSInitPeer preReach (initPeer ts cI rdy) tt
 rVWSInvariant2 (step preReach (recvMsg ts ∈SM-pre ready trans)) = rVWSRecvMsg2 preReach (recvMsg ts ∈SM-pre ready trans) tt
