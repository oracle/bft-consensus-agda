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
 previously sent by an honest peer.  A peer can also announce a
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
   announce : ℕ → Action
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
 initialStateAndMessages p _ = mkState p 0 nothing , []

 open RWST-do

 data handlerResult : Set where
   gotFirstAdvance  : PeerId → handlerResult
   confirmedAdvance : ℕ → handlerResult

 gFA-injective : ∀ {n m} → gotFirstAdvance n ≡ gotFirstAdvance m → n ≡ m
 gFA-injective refl = refl

 cA-injective : ∀ {n m} → confirmedAdvance n ≡ confirmedAdvance m → n ≡ m
 cA-injective refl = refl

{-
 _≟HR_ : (hr1 hr2 : handlerResult) → Dec (hr1 ≡ hr2)
 (gotFirstAdvance  _) ≟HR (confirmedAdvance _) = no λ ()
 (confirmedAdvance _) ≟HR (gotFirstAdvance  _) = no λ ()
 (gotFirstAdvance p1) ≟HR (gotFirstAdvance p2) with p1 ≟ p2
 ...| yes refl = yes refl
 ...| no  neq  = no (neq ∘ gFA-injective)
 (confirmedAdvance v1) ≟HR (confirmedAdvance v2) with v1 ≟ v2
 ...| yes refl = yes refl
 ...| no  neq  = no (neq ∘ cA-injective)
-}

 pureHandler : Message → Instant → State → Maybe handlerResult × List Action
 pureHandler msg ts st with st ^∙ maxSeen  <? msg ^∙ val
 ...| no  _  = nothing , []
 ...| yes newMax with msg ^∙ val ≟ suc (st ^∙ maxSeen)
 ...| no  _  = nothing , []
 ...| yes newIsNext with st ^∙ newValSender
 ...| nothing = just (gotFirstAdvance (msg ^∙ author)) , send (suc (msg ^∙ val)) ts ∷ []
 ...| just 1stSender = just (confirmedAdvance (msg ^∙ val)) , announce (msg ^∙ val) ∷ []

 handle : Message → Instant → RWST Unit Action State Unit
 handle msg ts = do  -- TODO: Check signature
   st ← get
   case proj₁ (pureHandler msg ts st) of
     λ { nothing    → pure unit
       ; (just (gotFirstAdvance  p)) → newValSender ∙= just p
       ; (just (confirmedAdvance v)) → do
           -- TODO: It's pretty weird to use the timestamp as a
           -- nondeterministic choice of recipient, but don't have any
           -- easy alternative currently
           maxSeen ∙= v
           newValSender ∙= nothing
       }
   tell (proj₂ (pureHandler msg ts st))


{-
 modifiesMaxSeen : ∀ {ppre ppost m now env}
                 → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m now) env ppre)
                 → ppost ^∙ maxSeen ≢ ppre ^∙ maxSeen
                 → Σ ℕ (λ v → pureHandler m ppre ≡ just (confirmedAdvance v))
 modifiesMaxSeen {ppre} {ppost} {m} upd change with pureHandler m ppre
 ...| nothing = ⊥-elim (change (cong :maxSeen upd))
 ...| just (gotFirstAdvance p)  = ⊥-elim (change (subst (λ s → :maxSeen ppost ≡ :maxSeen s) upd refl))
 ...| just (confirmedAdvance v) = v , refl
 -- What's the best systematic way to prove/represent the conditions required for a variable to change?
 maxSeenChangeCond : ∀ {ppre m v}
                   → pureHandler m ppre ≡ just (confirmedAdvance v)
                   → (v ≡ m ^∙ val)
                   × (v ≡ suc (ppre ^∙ maxSeen))
                   × Σ PeerId (((ppre ^∙ newValSender) ≡_) ∘ just)
 maxSeenChangeCond {ppre} {m} {v} isConf
   with pureHandler m ppre
 ...| just phr with phr ≟HR confirmedAdvance v
 ...| no  neq = ⊥-elim (neq (just-injective isConf))
 ...| yes phr≡ 
   with ppre ^∙ maxSeen  <? m ^∙ val
 ...| no  xx = ⊥-elim (maybe-⊥ isConf {!!})
 ...| yes newMax
   with m ^∙ val ≟ suc (ppre ^∙ maxSeen)
 ...| no xx1 = ⊥-elim (maybe-⊥ isConf {!!})
 ...| yes newIsNext
   with ppre ^∙ newValSender
 ...| nothing = ⊥-elim {!just-injective isConf!}
 ...| just xx = {!!}
-}

 exampleActionsToSends : State → Action → List (PeerId × Message)
 exampleActionsToSends s (announce _) = []
 exampleActionsToSends s (send n peer) =  (peer , (mkMessage (s ^∙ myId) n nothing)) ∷ []

 -- TODO: Use Meta to avoid "peeking"?
 dishonest : Message → PeerId → Set
 dishonest m peer with peer ≟ 0
 ...| no _  = ⊥
 ...| yes d = ⊤

 open import LibraBFT.Global.SystemModel
               Instant
               PeerId
               _≟_
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

 trivialInvariant : Invariant (const ⊤)
 trivialInvariant init = tt
 trivialInvariant (step s x) = tt

 -- Properties about transitions (some should go into SystemModel)

 

 -- Here is a less trivial, but (conceptually) easy invariant.  First
 -- prove it, then look for ways to streamline parts that will be
 -- common, such as:
 --   initializing a given peer establishes the invariant for that peer
 --   initializing another peer does not falsify the invariant for a given peer
 --   cheating does not affect peer states

 -- Informal argument
 --
 -- If the action is an initPeer     for p (by ≡ p), then its initial state has nothing, contradicting second premise
 -- If the action is an initPeer not for p (by ≢ p), then p's peerState does not change, and the inductive hypothesis carries the day
 -- If the action is a cheat for any process, it does not modify anyone's peerStates, so inductive hypothesis carries the day again
 -- If the action is a recvMessage, it only *establishes* the condition if the message needed exists

 -- If peer p has recorded that p' sent the next value, then p' did!
 
 recordedValueWasSent : SystemState → Set
 recordedValueWasSent st = ∀ {pSt curMax}
                           → (sender p : PeerId)
                           → lookup p (peerStates st) ≡ just pSt
                           → pSt ^∙ newValSender ≡ just sender
                           → pSt ^∙ maxSeen ≡ curMax
                           → Σ PeerId λ recip → Σ Message (λ msg → (recip , msg) ∈SM sentMessages st
                                                                 × WithVerSig msg
                                                                 × msg ^∙ author ≡ sender
                                                                 × msg ^∙ val ≡ suc curMax)

 rVWSInvariant2 : Invariant recordedValueWasSent
 rVWSInvariant2 {sysState _ .empty} init {pSt} sender p = ⊥-elim ∘ ((flip maybe-⊥) kvm-empty)

 rVWSInvariant2 (step {ts} {pre} {post} _ {by} theStep) {pSt} sender p pSt≡ r1 r2
   with         (lookup p) (peerStates post) |
        inspect (lookup p) (peerStates post)
 ...| nothing    | _ = ⊥-elim (maybe-⊥ pSt≡ refl)
 ...| just ppost | [ postxx ]
   with Maybe-≡-dec _≟_ (:newValSender ppost) (just sender)
 ...| no  neq rewrite (just-injective pSt≡) = ⊥-elim (neq r1)
 ...| yes zzz with   (lookup p) (peerStates pre) |
             inspect (lookup p) (peerStates pre)
 ...| nothing   | [ xx1 ]
   with initPeerLemma {theStep = theStep} xx1 postxx
 ...| refl , _ , xx4 rewrite xx4 = ⊥-elim (maybe-⊥ zzz refl)
 rVWSInvariant2 (step {ts} {pre} {post} preReach {by} theStep) {pSt} {curMax} sender p pSt≡ r1 r2
    | just ppost | [ postxx ]
    | yes  zzz
    | just ppre@(mkState id1 oldMax prevNewValSender) | [ prexx ] rewrite (just-injective pSt≡)
   with Maybe-≡-dec _≟_ (:newValSender ppre) (just sender)
 ...| yes refl
   with oldMax ≟ curMax
 ...| yes refl
   with rVWSInvariant2 preReach sender p prexx refl refl
 ...| zz1 , m , zz2 , zz3 = zz1 , m , msgs-stable theStep zz2 , zz3
 rVWSInvariant2 (step {ts} {pre} {post} preReach {by} theStep) {pSt} {curMax} sender p pSt≡ r1 r2
    | just ppost | [ postxx ]
    | yes  zzz
    | just ppre@(mkState id1 oldMax prevNewValSender) | [ prexx ]
    | yes sender≡
    | no maxChanged
    with p ≟ by
 ...| no neq2 rewrite sym (just-injective pSt≡) =
          ⊥-elim (neq2 (stepByOtherPreservesJ
                          ((_≢ curMax) ∘ :maxSeen)
                          theStep
                          prexx
                          postxx
                          maxChanged
                          λ z → z r2))
 rVWSInvariant2 (step {ts} {pre} {post} preReach {by} theStep) {pSt} {curMax} sender p pSt≡ r1 r2
    | just ppost | [ postxx ]
    | yes  zzz
    | just ppre@(mkState id1 oldMax prevNewValSender) | [ prexx ]
    | yes sender≡
    | no maxChanged          -- Therefore this is a confirmed advance, which means that newValSender ≡ nothing in the post state, contradicting zzz      BREAK DOWN INTO SMALLER LEMMAS
    | yes refl -- p ≡ by
    with theStep
 ...| initPeer _ cI rdy = ⊥-elim (maybe-⊥ r1 (cong :newValSender (proj₂ (proj₂ (initPeerLemma {theStep = theStep} rdy postxx)))))
 ...| cheat ts to m x rewrite just-injective pSt≡ | cheatPreservesPeerState {pre} {post} {by} {p} {ts} (cheat ts to m x) tt =
              ⊥-elim (maxChanged (trans (sym (cong :maxSeen (just-injective (trans (sym postxx) (trans (cheatPreservesPeerState {pre} {post} {by} {p} {ts} (cheat ts to m x) tt) prexx))))) r2))

 ...| recvMsg {m} {to} {_} {ppre1} {ppost1} ts ∈SM ready run
    with pureHandler m ts ppre1
 ...| nothing , acts = {!!}                       -- no change, contradicts zzz , neq
 ...| just (confirmedAdvance n) , acts  = {!!}    -- sets newValsender to nothing, contradicts zzz
 ...| just (gotFirstAdvance sndr') , acts = {!!}  -- sets newValSender to sndr'; if sndr' ≡ sender, m is the required message
                                                  --                             otherwise, contradicts zzz
 rVWSInvariant2 (step {ts} {pre} {post} _ {by} theStep) {pSt} sender p pSt≡ r1 r2
    | just ppost | [ postxx ]
    | yes  zzz
    | just ppre@(mkState id1 oldMax prevNewValSender) | [ prexx ]
    | no  neq          -- p's state changed, therefore p ≡ by
    with p ≟ by
 ...| no  neq2 rewrite sym (just-injective pSt≡) =
          ⊥-elim (neq2 (stepByOtherPreservesJ
                          ((_≢ (just sender)) ∘ :newValSender)
                          theStep
                          prexx
                          postxx
                          neq
                          λ z → z r1))
 ...| yes refl
    with theStep
 ...| initPeer ts cI rdy = ⊥-elim (maybe-⊥ r1 (cong :newValSender (proj₂ (proj₂ (initPeerLemma {pre} {post} {by} {p} {pSt} {ts} {theStep} rdy postxx)))))
 ...| cheat ts to m x rewrite cheatPreservesPeerState {pre} {post} {by} {p} {ts} (cheat ts to m x) tt =
              ⊥-elim (neq (trans (cong :newValSender (just-injective (trans (sym prexx) postxx))) r1))
 ...| recvMsg {m} {to} {_} {ppre1} {ppost1} ts ∈SM ready run
    with pureHandler m ts ppre1
 ...| nothing , acts = {!!}                       -- no change, contradicts zzz , neq
 ...| just (confirmedAdvance n) , acts  = {!!}    -- sets newValsender to nothing, contradicts zzz
 ...| just (gotFirstAdvance sndr') , acts = {!!}  -- sets newValSender to sndr'; if sndr' ≡ sender, m is the required message
                                                  --                             otherwise, contradicts zzz


{--

The above is too big and messy.  I want to be able to write more concise proofs that can be combined
together, heopfully eventually mirroring intuitive case analyses in common patterns.  Below I made a
small start that addresses only "cheat" steps.

--}


 rVWSInvariant : Invariant recordedValueWasSent

 rVWSCheat : ∀ {pre post by ts}
     → ReachableSystemState pre
     → (theStep : Step by pre ts post)
     → isCheatStep theStep
     → recordedValueWasSent post
 rVWSCheat preReach theStep isCheat {pSt} sender p pSt≡ sender≡ max≡
   with rVWSInvariant preReach sender p (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) sender≡ max≡
 ...| xx1 , xx2 , xx3 , xx4 = xx1 , xx2 , msgs-stable theStep xx3 , xx4

 rVWSInvariant init sender p x = ⊥-elim (maybe-⊥ x kvm-empty)

 rVWSInvariant (step preReach (cheat ts to m dis)) = rVWSCheat preReach (cheat ts to m dis) tt

 rVWSInvariant (step preReach (initPeer ts cI rdy)) = {!!}
 
 rVWSInvariant (step preReach (recvMsg ts ∈SM-pre ready trans)) = {!!}
