{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Abstract.Types using (Meta ; meta)
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
   fakePubKey : PeerId → PK
   fakePubKey-inj : ∀ {a1 a2} → fakePubKey a1 ≡ fakePubKey a2 → a1 ≡ a2

 _≟-PeerId_ : (p₁ p₂ : PeerId) → Dec (p₁ ≡ p₂)
 _≟-PeerId_ = _≟_

 data Message : Set

 record DirectMessage : Set where
   constructor mkDirectMessage
   field
     :to     : Meta PeerId
     :author : PeerId
     :val    : ℕ
     :sigMB  : Maybe Signature
 open DirectMessage

 unquoteDecl to   author   val   sigMB = mkLens (quote DirectMessage)
            (to ∷ author ∷ val ∷ sigMB ∷ [])

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

 isDirect : Message → Set
 isDirect (direct _) = ⊤
 isDirect (gossip _) = ⊥

 isGossip : Message → Set
 isGossip (direct _) = ⊥
 isGossip (gossip _) = ⊤

 getAuthor : Message → PeerId
 getAuthor (direct m) = m ^∙ author
 getAuthor (gossip m) = m ^∙ gmAuthor

 data Output : Set where
   announce : ℕ → Output           -- This is analogous to "commit"
   send     : ℕ → PeerId → Output

 open import LibraBFT.Global.SystemModelPrelude {Message}

 canInit : PeerId → Set
 canInit p = ⊤

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

 initialStateAndMessages : (p : PeerId) → canInit p → State × List Action
 initialStateAndMessages p _ = mkState p (fakePubKey p) 0 nothing , []  -- TODO : send something!

 postulate
   Signed-pi-Direct : (m : DirectMessage)
                    → (is1 is2 : (Is-just ∘ :sigMB) m)
                    → is1 ≡ is2
   Signed-pi-Gossip : ∀ (m : GossipMessage)
                    → (is1 is2 : (Is-just ∘ :gmSigMB) m)
                    → is1 ≡ is2

 instance
   sig-DirectMessage : WithSig DirectMessage
   sig-DirectMessage = record
      { Signed         = Is-just ∘ :sigMB
      ; Signed-pi      = Signed-pi-Direct
      ; isSigned?      = λ m → Maybe-Any-dec (λ _ → yes tt) (m ^∙ sigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ dm → concat ( encode (dm ^∙ author)
                                       ∷ encode (dm ^∙ val)
                                       ∷ [])
      }

   sig-GossipMessage : WithSig GossipMessage
   sig-GossipMessage = record
      { Signed         = Is-just ∘ :gmSigMB
      ; Signed-pi      = Signed-pi-Gossip
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

 -- TODO: move to prelude or find in standard library?
 overSecond : ∀ {A B C : Set} → (A → B) → (C × A) → (C × B)
 overSecond f (c , a) = (c , f a)

 tupleRefl : ∀ {A B : Set} {a : A} {b1 b2 : B}
           → b1 ≡ b2
           → (a , b1) ≡ (a , b2)
 tupleRefl refl = refl

 -- Send outputs cause messages to be sent, accounce outputs do not
 exampleOutputToSends : State → Output → List Action
 exampleOutputToSends s (announce _) = []
 exampleOutputToSends s (send n peer) = send (direct (mkDirectMessage (meta peer) (s ^∙ myId) n nothing)) ∷ []  -- TODO: sign message

 outputToSends : State → (State × List Output) → (State × List Action)
 outputToSends st = overSecond (concat ∘ List-map (exampleOutputToSends st))

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

 runHandler : State → RWST Unit Output State Unit → State × List Action
 runHandler st handler = outputToSends st (proj₂ (RWST-run handler unit st))

 stepPeerD : (msg : DirectMessage) → Instant → State → State × List Action
 stepPeerD msg ts st
    with sigCheckOutcomeFor (fakePubKey (msg ^∙ author)) msg
 ...| notSigned   = (st , [])
 ...| checkFailed = (st , [])
 ...| sigVerified = runHandler st (handle msg ts)

 stepPeerG : (msg : GossipMessage) → Instant → State → State × List Action
 stepPeerG msg ts st
     with sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor)) msg
 ...| notSigned   = (st , [])
 ...| checkFailed = (st , [])
 ...| sigVerified = stepPeerD (msg ^∙ original) ts st

 stepPeer : (msg : Message) → Instant → State → State × List Action
 stepPeer (direct msg) ts st = stepPeerD msg ts st
 stepPeer (gossip msg) ts st = stepPeerG msg ts st


 notSignedNoEffectD : ∀ {msg ts st}
                    → sigCheckOutcomeFor (fakePubKey (msg ^∙ author)) msg ≡ notSigned
                    → stepPeer (direct msg) ts st ≡ (st , [])
 notSignedNoEffectD {msg} {ts} {st} prf rewrite prf = refl

 notSignedNoEffectG : ∀ {msg ts st}
                    → sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor)) msg ≡ notSigned
                    → stepPeer (gossip msg) ts st ≡ (st , [])
 notSignedNoEffectG {msg} {ts} {st} prf rewrite prf = refl

 notVerifiedNoEffectD : ∀ {msg ts st}
                      → sigCheckOutcomeFor (fakePubKey (msg ^∙ author)) msg ≡ checkFailed
                      → stepPeer (direct msg) ts st ≡ (st , [])
 notVerifiedNoEffectD {msg} {ts} {st} nv rewrite nv = refl

 notVerifiedNoEffectG : ∀ {msg ts st}
                      → sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor)) msg ≡ checkFailed
                      → stepPeer (gossip msg) ts st ≡ (st , [])
 notVerifiedNoEffectG {msg} {ts} {st} nv rewrite nv = refl

 verifiedGossipEffect≡ : ∀ {msg : GossipMessage}{ts st}
                       → sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor)) msg ≡ sigVerified
                       → stepPeer (gossip msg) ts st ≡ stepPeer (direct (:original msg)) ts st
 verifiedGossipEffect≡ {msg} {ts} {st} prf rewrite prf
    with sigCheckOutcomeFor (fakePubKey ((msg ^∙ original) ^∙ author)) msg
 ...| notSigned   = refl
 ...| checkFailed = refl
 ...| sigVerified = refl


{-
 unverifiedGossipNoEffect1 : ∀ {msg ts st}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (fakePubKey (msg ^∙ gmAuthor)) msg ≡ nothing
   → stepPeer (gossip msg) ts st ≡ (st , [])
 unverifiedGossipNoEffect1 {msg} {ts} {st} prf rewrite prf = refl

 unverifiedGossipNoEffect2 : ∀ {msg ts st ver}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (fakePubKey (msg ^∙ gmAuthor)) msg ≡ just ver
   → check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (fakePubKey ((:original msg) ^∙ author)) (:original msg) ≡ nothing
   → stepPeer (gossip msg) ts st ≡ (st , [])
 unverifiedGossipNoEffect2 {msg} {ts} {st} prf1 prf2 rewrite prf1 | prf2 = refl

 verifiedGossipEffect : ∀ {msg ts st ver ver'}
   → check-signature {GossipMessage} ⦃ sig-GossipMessage ⦄ (fakePubKey (msg ^∙ gmAuthor)) msg ≡ just ver
   → check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (fakePubKey ((:original msg) ^∙ author)) (:original msg) ≡ just ver'
   → stepPeer (gossip msg) ts st ≡ outputToSends st (proj₂ (RWST-run (handleDirect (:original msg) ts) unit st))
 verifiedGossipEffect {msg} {ts} {st} prf1 prf2 rewrite prf1 | prf2 = refl

 handleDirect≡ : {m : DirectMessage}
               → {wvs : WithVerSig m}
               → check-signature (fakePubKey (m ^∙ author)) m ≡ just wvs
               → (ts : Instant)
               → State
               → handleDirectVerified m wvs ts ≡ handleDirect m ts
 handleDirect≡ {msg} {wvs} prf ts st
     with (check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (fakePubKey (msg ^∙ author))) msg | inspect
          (check-signature {DirectMessage} ⦃ sig-DirectMessage ⦄ (fakePubKey (msg ^∙ author))) msg
 ...| nothing  | [ R' ] = ⊥-elim (maybe-⊥ prf refl)
 ...| just ver | [ R' ] = refl


-}



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

 modifiesNewSenderVal : ∀ {m : DirectMessage}{ppre ppost ts v}
                      → ppost ≡ (proj₁ ∘ proj₂) (RWST-run (handle m ts) unit ppre)
                      → ppre  ^∙ newValSender ≢ ppost ^∙ newValSender
                      → ppost ^∙ newValSender ≡ just v
                      → proj₁ (pureHandler m ts ppre) ≡ gotFirstAdvance v
                      × ppost ^∙ maxSeen ≡ ppre ^∙ maxSeen
 modifiesNewSenderVal {m} {ppre} {ppost} {ts} {v} run≡ pre≢post jv rewrite run≡
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

 -- Handling two direct messages that are both verifiably signed and have the same signature has the
 -- same effect (post state and outputs).  TODO: Probably can be simplified if we require/prove
 -- proof irrelevance for isSigned.
 --
 -- TODO: Prove this postulate.  This will require an assumption that signatures are injective, and
 -- that the encodings used to generate and concatenate the signable fields are also injective.

 postulate
   sameSignatureSameEffect :
     ∀ {ppre}{ts}{m m' : DirectMessage}
     → (wvs  : WithVerSig {DirectMessage} m)
     → (wvs' : WithVerSig {DirectMessage} m')
     → signature {DirectMessage} m' (isSigned wvs') ≡ signature {DirectMessage} m (isSigned wvs)
     → stepPeer (direct m') ts ppre ≡ stepPeer (direct m) ts ppre

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
               State
               canInit
               initialStateAndMessages
               stepPeer
               dishonest

 -- This postulate captures the assumption that one peer p0 cannot create a verifiably signed
 -- message by another peer p1 unless p1 is dishonest for that message (*, see notes below).
 -- However, nothing here specifically refers to the peers.  So, in fact, a peer can create and sign
 -- a message with its own key, and if it doesn't send it (or hasn't yet), then this postulate would
 -- suggest that the peer must be dishonest.  I think this is OK because an honest peer (which runs
 -- the code) would never conclude that it is dishonest itself.  In fact, at this stage, honest
 -- peers don't specifically conclude anyone is dishonest; they just use this property to reason
 -- about the (at least one, by the BFT assumption) honest peers that contributed to a quorum.  It
 -- might be preferable to make the postulate specifically about other peers, but then we have to
 -- get into who has what public key, etc.  I think we should do something more refined here.  In
 -- particular, this postulate would not be true (even for "other" peers") if all peers had the same
 -- key pair.  We do assume that this is not the case (see fakePubKey-inj above), but that is not
 -- referenced here.  TODO: We should refine this postulate when we address key pairs properly.
 --
 -- (*) What does it mean for p1 to be "dishonest for a message"?  This is motivated by the fact
 -- that assumptions about peer honest are at the granularity of epochs.  Thus, a peer may be honest
 -- for one epoch and dishonest for another.  Therefore, whether a message was sent by an honest or
 -- dishonest peer is a function of that message, as well as of which peers are dishonest for the
 -- epoch of the message.

 -- NOTES:
 --
 -- (0) We need this only for direct messages, because we don't use it for gossip message.

 postulate
   sentUnlessDishonest : ∀ {m : DirectMessage}{st : SystemState}⦃ sm : WithSig DirectMessage ⦄
                       → (wvs : WithVerSig {DirectMessage} ⦃ sm ⦄ m)
                       → dishonest (direct m)
                         ⊎ ∃[ m' ] ( direct m' ∈SM sentMessages st
                                   × Σ (WithVerSig ⦃ sig-DirectMessage ⦄  m')
                                       (λ wvs' → signature m' (isSigned wvs') ≡
                                                 signature m  (isSigned wvs)))

 -- The following functions enable us to conveniently prove that handling a message that is not
 -- correctly signed preserves any invariant (because we do not update any state in that case).

 -- TODO: Somewhat of a DRY fail here.  Unify?
 verifySigPreservesD : ∀ {msg : DirectMessage}{pre post by ts}
                     → (P : SystemState → Set)
                     → (theStep : Step pre post)
                     → (iR : isRecvMsg theStep)
                     → P pre
                     → lookup by (peerStates pre) ≡ just (ppreOf iR)
                     → stepPeer (direct msg) ts (ppreOf iR) ≡ (ppostOf iR , actsOf iR)
                     → P post ⊎ sigCheckOutcomeFor (fakePubKey (msg ^∙ author)) msg ≡ sigVerified
 verifySigPreservesD {msg} {pre} {post} {by} {ts} P theStep iR Ppre rdy run≡
    with  sigCheckOutcomeFor (fakePubKey (msg ^∙ author))  msg | inspect
         (sigCheckOutcomeFor (fakePubKey (msg ^∙ author))) msg
 ...| notSigned   | [ R ] rewrite R = inj₁ (InvariantStates≡ P
                                              (noChangePreservesState theStep iR (cong proj₁ (sym run≡))
                                                                                 (cong proj₂ (sym run≡)))
                                           Ppre)
 ...| checkFailed | [ R ] rewrite R = inj₁ (InvariantStates≡ P
                                              (noChangePreservesState theStep iR (cong proj₁ (sym run≡))
                                                                                (cong proj₂ (sym run≡)))
                                           Ppre)
 ...| sigVerified | [ R ] rewrite R = inj₂ refl

 -- Essentially the same as verifySigPreservesD
 verifySigPreservesG  : ∀ {msg : GossipMessage}{pre post by ts}
                      → (P : SystemState → Set)
                      → (theStep : Step pre post)
                      → (iR : isRecvMsg theStep)
                      → P pre
                      → lookup by (peerStates pre) ≡ just (ppreOf iR)
                      → stepPeer (gossip msg) ts (ppreOf iR) ≡ (ppostOf iR , actsOf iR)
                      → P post ⊎ sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor)) msg ≡ sigVerified
 verifySigPreservesG {msg} {pre} {post} {by} {ts} P theStep iR Ppre rdy run≡
    with  sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor))  msg | inspect
         (sigCheckOutcomeFor (fakePubKey (msg ^∙ gmAuthor))) msg
 ...| notSigned   | [ R ] rewrite R = inj₁ (InvariantStates≡ P
                                              (noChangePreservesState theStep iR (cong proj₁ (sym run≡))
                                                                                 (cong proj₂ (sym run≡)))
                                           Ppre)
 ...| checkFailed | [ R ] rewrite R = inj₁ (InvariantStates≡ P
                                              (noChangePreservesState theStep iR (cong proj₁ (sym run≡))
                                                                                (cong proj₂ (sym run≡)))
                                           Ppre)
 ...| sigVerified | [ R ] rewrite R = inj₂ refl

 -- The following (conceptually) easy invariant states that if peer p has recorded that p' sent the
 -- next value, then p' actually did sent it!

 -- Informal argument
 --
 -- If the action is an initPeer     for p (by ≡ p), then its initial state has nothing, contradicting second premise
 -- If the action is an initPeer not for p (by ≢ p), then p's peerState does not change, and the inductive hypothesis carries the day
 -- If the action is a cheat for any process, it does not modify anyone's peerStates, so inductive hypothesis carries the day again
 -- If the action is a recvMessage, it only *establishes* the condition if the message needed exists



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
 rVWSConsCast {pre = pre} {post = post} (mkRVWSConsequent m sig ∈SM-pre a v) theStep =
              mkRVWSConsequent m sig (allegedlySentStable {direct m} {pre} {post} theStep ∈SM-pre) a v

 RecordedValueWasAllegedlySent : SystemState → Set
 RecordedValueWasAllegedlySent st = ∀ {p pSt curMax}
                               → (sender : PeerId)
                               → lookup p (peerStates st) ≡ just pSt
                               → pSt ^∙ newValSender ≡ just sender
                               → pSt ^∙ maxSeen ≡ curMax
                               → RVWSConsequent sender curMax st

 rVWSInvariant : Invariant RecordedValueWasAllegedlySent

 rVWSCheat : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → isCheatStep theStep
     → RecordedValueWasAllegedlySent post
 rVWSCheat {pre} {post} preReach theStep isCheat {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
   -- A cheat step does cannot "unsend" messages and does not affect anyone's state
   with rVWSInvariant preReach sender (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep 
 
 rVWSInitPeer : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → isInitPeer theStep  -- Not needed in this example as it is trivial; keeping it to make example more general
     → RecordedValueWasAllegedlySent post
 rVWSInitPeer {pre} {post} preReach theStep _ {p} {pSt} sender pSt≡ sender≡ max≡
   with peerOf theStep ≟ p
 ...| yes refl
   with theStep    -- TODO: Why can't I avoid this with clause by using rdyOf below?
                   -- It would simplify this proof by allowing this case to be in one line,
                   -- thus avoiding the need for spelling out the next case explicitly.
 ...| initPeer _ _ _ rdy
      -- After initializing p, the antecedent does not hold because :newValSender (lookup p (peerState post)) ≡ nothing
      = ⊥-elim (maybe-⊥ sender≡ (cong :newValSender (just-injective (trans (sym pSt≡) (lookup-correct rdy)))))

 rVWSInitPeer {pre} {post} preReach theStep _ {p} {pSt} sender pSt≡ sender≡ max≡
    | no xx
      -- Initializing "by" does not falsify the invariant for p ≢ by
   with rVWSInvariant preReach sender (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsgD : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → (iR : isRecvMsg theStep)
     → isDirect (msgOf iR)
     → RecordedValueWasAllegedlySent post
 rVWSRecvMsgD {pre} {post} preReach
             theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ isD {p} sender pSt≡ sender≡ max≡
    with verifySigPreservesD {msg = msg} RecordedValueWasAllegedlySent theStep tt (rVWSInvariant preReach) rdy run≡ 
 ...| inj₁ done = done sender pSt≡ sender≡ max≡
 ...| inj₂ _
    with peerOf theStep ≟ p
 ...| no xx
    -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
    with rVWSInvariant preReach sender (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsgD {pre} {post} preReach
             theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
    | inj₂ _
    | yes refl

    -- Stash for later use: pSt ≡ ppost because of the "ready" condition for the step
    --                      definition of ppost
    with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡ | cong proj₁ run≡
 ...| pSt≡ppost | ppost≡
    -- The step is by p; consider cases of whether the antecedent holds in the prestate
    with Maybe-≡-dec _≟-PeerId_ (:newValSender ppre) (just sender) | curMax ≟ :maxSeen ppre
 ...| yes refl | yes refl
    -- It does, so the inductive hypothesis ensures the relevant message was sent before, and the step does not "unsend" it
    with rVWSInvariant preReach {pSt = ppre} sender rdy refl refl
 ...| preCons = rVWSConsCast preCons theStep

 rVWSRecvMsgD {pre} {post} preReach
             (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ isD {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
    | inj₂ sigVer
    | yes refl
    | pSt≡ppost | ppost≡
    | no nVSChanged | curMax≟maxSeen
    with sigVerifiedVerSigCS sigVer
 ...| (_ , _ , wvs , R)
    rewrite R
    -- newValSender ≢ sender in the prestate. Because newValSender ≡ sender in the poststate, the handler
    -- result must be just (gotFirstAdvance sender)
    with (sym pSt≡ppost) | (sym sender≡)
 ...| refl | refl
    with modifiesNewSenderVal {msg} {ppre} {ppost} {ts} {sender} (sym ppost≡) nVSChanged sender≡
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
 ...| inj₁ dis   = mkRVWSConsequent msg wvs (inj₁ dis) auth≡ val≡
 ...| inj₂ sentM = mkRVWSConsequent msg wvs (inj₂ (∈SM-stable-list
                                                    {actionsToMessages acts}
                                                    {sentMessages pre}
                                                    {direct msg}
                                                    (sentM)))
                                            auth≡ val≡
 rVWSRecvMsgD {pre} {post} preReach
             (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) _ _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
    | inj₂ sigVer
    | yes refl
    | pSt≡ppost | ppost≡
    | yes refl | no curMaxChanged
    -- Because maxSeen changed, the handlerResult is a confirmedAdvance
    with (sym pSt≡ppost) | (sym max≡)
 ...| refl | refl rewrite sigVer
    with modifiesMaxSeen {ppre} {ppost} {msg} (sym ppost≡)(curMaxChanged ∘ sym)
 ...| isConfirmedAdvance
    -- Therefore, the step sets newValSender to nothing, thus ensuring that antecedent does not hold
    -- in the poststate
    -- Here we use the "effects" lemma, which is a little less convenient, but more general.  Keeping it
    -- this way for demonstration purposes.
    with cAEffect {ppre} {ppost} {msg} (sym ppost≡) isConfirmedAdvance
 ...| senderBecomesNothing , _ = ⊥-elim (maybe-⊥ sender≡ senderBecomesNothing)

 -- For gossip messages, we simply verify the signature and if it verifies, handle the original
 -- message it contains
 rVWSRecvMsgG : ∀ {pre post}
     → ReachableSystemState pre
     → (theStep : Step pre post)
     → (iR : isRecvMsg theStep)
     → isGossip (msgOf iR)
     → RecordedValueWasAllegedlySent post
 rVWSRecvMsgG {pre} {post} preReach
             (recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ _
             -- It's annoying that this case spells out all the parameters of rVWSInvariant just to then consume them, but they are needed for the next case
    with verifySigPreservesG {msg = msg} RecordedValueWasAllegedlySent
                             (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡)
                             tt (rVWSInvariant preReach) rdy run≡
 ...| inj₁ done = done
 ...| inj₂ gmVer rewrite gmVer
    -- Effect of verified gossip message is equivalent to effect of direct message it contains
    with trans (verifiedGossipEffect≡ {msg} {ts} {ppre} gmVer) run≡
 ...| run≡'
    with verifySigPreservesD {msg = msg ^∙ original} RecordedValueWasAllegedlySent
                             (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡')
                             tt (rVWSInvariant preReach) rdy run≡
 ...| inj₁ done  = done
 ...| inj₂ dmVer
    with sigVerifiedVerSigCS dmVer
 ...| (sc , ver , wvs , wvsProp)
    rewrite dmVer
    -- Here we need to construct a message that contains the same signature as the original message and verifies.
    with sentUnlessDishonest { :original msg } {pre} ⦃ sig-DirectMessage ⦄
                             (record { isSigned  = isSigned wvs
                                     ; verWithPK = verWithPK wvs
                                     ; verified  = verified wvs
                                     })
 ...| inj₁ senderDishonest rewrite dmVer | gmVer =
           rVWSRecvMsgD {pre} {post} preReach
                        (recvMsg {pre} {direct (:original msg)} {42}
                                 {ppre} {ppost} {acts} by ts (inj₁ senderDishonest) rdy run≡') tt tt
 ...| inj₂ (m' , m'∈SM , wvs' , sigs≡)
      -- Now we know that we have a message (m') that has been sent (m'∈SM), and it verifies (wvs')
      -- with the same signature (sigs≡) as m.  This does not prove that it is the same message, and
      -- indeed it may not be (fields not covered by the signature may be different, and fields
      -- covered by the signature may be different too, if we assume signature collisions are
      -- possible).  Most importantly, we don't know that the effect of handling m' will be the same
      -- as that of handling :original msg.  We will need to prove that.  It encompasses the
      -- question of whether the signature covers all the necessary fields.  Note that it could be
      -- possible that there is a correct algorithm that does not have this property.  For example,
      -- it could be that the intended recipient is different in the two messages, so if an
      -- algorithm recorded in some way the intended recipient, then handling the two messages would
      -- not have identical effect, even though this would not affect correctness.  In that case,
      -- we'd need to prove that the effects of the two messages are "sufficiently" the same to
      -- ensure correctness (somewhat similar to what we've done for QCs.)
     with Signed-pi-Direct (:original msg) (isSigned wvs) sc
 ...| isSigned≡
     with sameSignatureSameEffect {ppre} {ts} {:original msg} {m'} wvs wvs'
 ...| sameEffect rewrite dmVer | gmVer =
           rVWSRecvMsgD {pre} {post} preReach
                        (recvMsg {pre} {direct m'} { 42 }  -- See comment above regarding 42
                           {ppre} {ppost} {acts} by ts (inj₂ m'∈SM) rdy
                           (trans (sameEffect sigs≡) run≡))
                           tt tt
 rVWSInvariant init sender x = ⊥-elim (maybe-⊥ x kvm-empty)
 rVWSInvariant (step preReach (cheat by ts m dis))     = rVWSCheat preReach (cheat by ts m dis) tt
 rVWSInvariant (step preReach (initPeer by ts cI rdy)) = rVWSInitPeer preReach (initPeer by ts cI rdy) tt
 rVWSInvariant (step {pre} preReach (recvMsg {direct msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans))
               = rVWSRecvMsgD preReach (recvMsg {pre} {direct msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans) tt tt
 rVWSInvariant (step {pre} preReach (recvMsg {gossip msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans))
               = rVWSRecvMsgG preReach (recvMsg {pre} {gossip msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans) tt tt

--  -- Another way of approaching the proof is to do case analysis on pureHandler results.
--  -- In this example, if proj₁ (pureHandler msg ts ppre) =
--  --   nothing              -- then the antecedent holds in the prestate, so the inductive hypothesis and ∈SM-stable-list suffice
--  --   confirmedAdvance _   -- then the effect is to set newValSender to nothing, ensuring the antecedent does not hold
--  --   gotFirstAdvance  p'  -- requires case analysis on whether p' ≡ p and maxSeen ppre and the message contents
--  rVWSInvariant2 : Invariant RecordedValueWasAllegedlySent

--  rVWSRecvMsg2D : ∀ {pre post}
--      → ReachableSystemState pre
--      → (theStep : Step pre post)
--      → (iR : isRecvMsg theStep)
--      → isDirect (msgOf iR)
--      → RecordedValueWasAllegedlySent post
--  rVWSRecvMsg2D {pre} {post} preReach
--     {- *** -}  theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
--     with verifySigDirect {msg = msg} RecordedValueWasAllegedlySent theStep isRecv (rVWSInvariant preReach) rdy run≡
--  ...| inj₁ done = done sender pSt≡ sender≡ max≡
--  ...| inj₂ _
--     with peerOf theStep ≟ p
--  ...| no xx
--     -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
--     with rVWSInvariant preReach sender (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) sender≡ max≡
--  ...| preCons = rVWSConsCast preCons theStep

--  rVWSRecvMsg2D {pre} {post} preReach
--     {- *** -}  (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
--     | inj₂ (ver , R , pks≡)
--     | yes refl
--     rewrite R
--     with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡ | cong proj₁ (sym run≡)
--  ...| pSt≡ppost | ppost≡
--     with proj₁ (pureHandler msg ts ppre) ≟HR noChange
--  ...| yes hR≡noChange
--     with nothingNoEffect {ppre} {ppost} {msg} {ts} hR≡noChange ppost≡
--  ...| noEffect
--     with pSt≡ppost | sym noEffect
--  ...| refl | refl
--     with rVWSInvariant preReach {pSt = ppre} sender rdy sender≡ max≡
--  ...| preCons = rVWSConsCast preCons (recvMsg {pre} {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy
--                                               (subst ((_≡ ppost , acts) ∘ (runHandler ppre))
--                                                      (handleDirect≡ {msg} {ver} R ts ppre)
--                                                      run≡))

--                                       -- Because of the rewrite R above, Agda no longer recognizes
--                                       -- that run≡ is

--  rVWSRecvMsg2D {pre} {post} preReach
--              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
--     | inj₂ (ver , R , pks≡)
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
--  ...| auth≡ , val≡ = mkRVWSConsequent msg ver
--                           (allegedlySentStable {direct msg} {pre} {post}
--                                                (recvMsg {pre} {direct msg} {to} {ppre} {ppost} {acts}
--                                                         by ts ∈SM-pre rdy
--                                                         (subst ((_≡ ppost , acts) ∘ (runHandler ppre))
--                                                                (handleDirect≡ {msg} {ver} R ts ppre)
--                                                                run≡))
--                                                ∈SM-pre)
--                           auth≡ val≡

--  rVWSRecvMsg2D {pre} {post} preReach
--              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) _ _ {p} {pSt} {curMax} sender pSt≡ sender≡ max≡
--     | inj₂ (_ , R , _)
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
--  -- message it contains.
--  -- NOTE: this is just a cut-and-paste from the same case in rVWSRecvMsgG
--  rVWSRecvMsg2G : ∀ {pre post}
--     → ReachableSystemState pre
--     → (theStep : Step pre post)
--     → (iR : isRecvMsg theStep)
--     → isGossip (msgOf iR)
--     → RecordedValueWasAllegedlySent post
--  rVWSRecvMsg2G {pre} {post} preReach
--              (recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) _ _
--     with verifySigGossip {msg = msg} RecordedValueWasAllegedlySent (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) tt (rVWSInvariant preReach) rdy run≡
--  ...| inj₁ done = done
--  ...| inj₂ (ver' , R') rewrite R'
--     -- This is somewhat redundant with verifySig*, but couldn't quite use it.  TODO: try again, think about unverifiedgossipnoeffect2
--     with check-signature (fakePubKey ((:original msg) ^∙ author))  (:original msg) | inspect
--         (check-signature (fakePubKey ((:original msg) ^∙ author))) (:original msg)
--  ...| nothing | [ R'' ]
--               = (InvariantStates≡
--                   RecordedValueWasAllegedlySent
--                   (noChangePreservesState
--                     (recvMsg {pre} {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy (trans (unverifiedGossipNoEffect2 R' R'') run≡))
--                     tt
--                     (cong proj₁ (sym run≡))
--                     (cong proj₂ (sym run≡)))
--                   (rVWSInvariant preReach))
--  ...| (just ver'') | [ R'' ] rewrite R' | R''
--      with verifiedGossipEffect {msg} {ts} {ppre} {ver'} {ver''} R' R''
--  ...| xxy

--     -- Here we need to construct a message that contains the same signature as the original message and verifies.
--     with sentUnlessDishonest { :original msg } {pre} ⦃ sig-DirectMessage ⦄
--                              (record { isSigned  = isSigned ver''
--                                      ; verWithPK = verWithPK ver''
--                                      ; verified  = verified ver''
--                                      })
--  ...| inj₁ senderDishonest rewrite R'' | R' =
--            rVWSRecvMsgD {pre} {post} preReach
--                         (recvMsg {pre} {direct (:original msg)} { 42 }
--                           {ppre} {ppost} {acts} by ts (inj₁ senderDishonest) rdy (trans xxy run≡)) tt tt
--                          -- Re: 42.  We just have to provide *some* recipient.  It
--                          -- would be tidier if the Gossip message included the
--                          -- original "to" peer, so we could keep it the same, but it
--                          -- doesn't matter much.
--  ...| inj₂ (m' , hs , hs' , is≡ , sigs≡ , (wvs' , is≡') , xx) rewrite R'' | R'
--    with sameSignatureSameEffect {ppre} {ts} {:original msg} {m'} {hs} {hs'} ver'' is≡
--                                 wvs' is≡' sigs≡
--  ...| sameEffect =
--       -- Now we know that we have a verifiably signed message m' that has been sent.  It has the
--       -- same signature as the one (:original msg) whose signature we have verified (ver'').
--       -- However, this does not prove that it is the same message, and indeed it may not be (fields
--       -- not covered by the signature may be different, and fields covered by the signature may be
--       -- different too, if we assume signature collisions are possible).  Most importantly, we don't
--       -- know that the effect of handling m' will be the same as that of handling :original msg.  We
--       -- will need to prove that.  It encompasses the question of whether the signature covers all
--       -- the necessary fields.  Note that it could be possible that there is a correct algorithm
--       -- that does not have this property.  For example, it could be that the intended recipient is
--       -- different in the two messages, so if an algorithm recorded in some way the intended
--       -- recipient, then handling the two messages would not have identical effect, even though this
--       -- would not affect correctness.  In that case, we'd need to prove that the effects of the two
--       -- messages are "sufficiently" the same to ensure correctness (somewhat similar to what we've
--       -- done for QCs.)
--            rVWSRecvMsgD {pre} {post} preReach
--                         (recvMsg {pre} {direct m'} { 42 }  -- See comment above regarding 42
--                            {ppre} {ppost} {acts} by ts (inj₂ xx) rdy
--                            (trans sameEffect (trans xxy run≡)))
--                            tt tt
--  -- Note that only the recvMsg cases are different; the rest are inherited from the previous proof
--  rVWSInvariant2 init sender x = ⊥-elim (maybe-⊥ x kvm-empty)
--  rVWSInvariant2 (step preReach (cheat by ts m dis))                 = rVWSCheat preReach (cheat by ts m dis) tt
--  rVWSInvariant2 (step preReach (initPeer by ts cI rdy))             = rVWSInitPeer preReach (initPeer by ts cI rdy) tt
--  rVWSInvariant2 (step {pre} preReach (recvMsg {direct msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans))
--                  = rVWSRecvMsg2D preReach (recvMsg {pre} {direct msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans) tt tt
--  rVWSInvariant2 (step {pre} preReach (recvMsg {gossip msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans))
--                 = rVWSRecvMsg2G preReach (recvMsg {pre} {gossip msg} {ppre} {ppost} {acts} by ts ∈SM-pre ready trans) tt tt

--  -----------------------------------------------------------------------------------------

-- -- --  record CVSB2Consequent (sender1 sender2 : PeerId) (curMax : ℕ) (st : SystemState) : Set where
-- -- --    constructor mkCVSB2Consequent
-- -- --    field
-- -- --      senders≢ : sender2 ≢ sender1
-- -- --      msg1     : RVWSConsequent sender1 curMax st
-- -- --      msg2     : RVWSConsequent sender2 curMax st
-- -- --  open CVSB2Consequent

-- -- --  cVSB2ConsCast : ∀ {sender1 sender2 curMax pre post}
-- -- --                → (preCons : CVSB2Consequent sender1 sender2 curMax pre)
-- -- --                → (to (msg1 preCons) , direct (m (msg1 preCons))) ∈SM (sentMessages post)
-- -- --                → (to (msg2 preCons) , direct (m (msg2 preCons))) ∈SM (sentMessages post)
-- -- --                → CVSB2Consequent sender1 sender2 curMax post
-- -- --  cVSB2ConsCast (mkCVSB2Consequent senders≢ xx1 xx2) ∈SM1-post ∈SM2-post =
-- -- --                 mkCVSB2Consequent
-- -- --                   senders≢
-- -- --                   (rVWSConsCast xx1 ∈SM1-post)
-- -- --                   (rVWSConsCast xx2 ∈SM2-post)

-- -- --  -- If an honest peer has recorded the maximum value seen as suc curMax,
-- -- --  -- then two different peers have sent messages with value curMax
-- -- --  CommittedValueWasSentBy2 : SystemState → Set
-- -- --  CommittedValueWasSentBy2 st = ∀ {pSt curMax p}
-- -- --                           → lookup p (peerStates st) ≡ just pSt
-- -- --                           → pSt ^∙ maxSeen ≡ suc curMax
-- -- --                           → ∃[ sender1 ] ∃[ sender2 ] (CVSB2Consequent sender1 sender2 curMax st)

-- -- --  cVSB2Invariant : Invariant CommittedValueWasSentBy2

-- -- --  cVSB2Cheat : ∀ {pre post}
-- -- --      → ReachableSystemState pre
-- -- --      → (theStep : Step pre post)
-- -- --      → isCheatStep theStep
-- -- --      → CommittedValueWasSentBy2 post
-- -- --  cVSB2Cheat preReach theStep isCheat {pSt} {curMax} {p} pSt≡ max≡
-- -- --    -- A cheat step does cannot "unsend" messages and does not affect anyone's state
-- -- --    with cVSB2Invariant preReach (trans (sym (cheatPreservesPeerState theStep isCheat)) pSt≡) max≡
-- -- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- -- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- -- --  cVSB2InitPeer : ∀ {pre post}
-- -- --      → ReachableSystemState pre
-- -- --      → (theStep : Step pre post)
-- -- --      → isInitPeer theStep
-- -- --      → CommittedValueWasSentBy2 post
-- -- --  cVSB2InitPeer {pre} {post} preReach theStep _ {pSt} {curMax} {p} pSt≡ max≡
-- -- --    with peerOf theStep ≟ p
-- -- --  ...| yes refl
-- -- --    with theStep
-- -- --  ...| initPeer _ _ _ rdy
-- -- --       -- After initializing p, the antecedent does not hold because :curMax ≡ 0
-- -- --    with just-injective (trans (sym pSt≡) (lookup-correct rdy))
-- -- --  ...| xxx
-- -- --       = ⊥-elim (1+n≢0 {curMax} (trans (sym max≡) (cong :maxSeen xxx)))

-- -- --  cVSB2InitPeer {pre} {post} preReach theStep _ {pSt} {curMax} {p} pSt≡ max≡
-- -- --     | no xx
-- -- --       -- Initializing "by" does not falsify the invariant for p ≢ by
-- -- --    with cVSB2Invariant preReach (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) max≡
-- -- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- -- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- -- --  cVSB2RecvMsg : ∀ {pre post}
-- -- --      → ReachableSystemState pre
-- -- --      → (theStep : Step pre post)
-- -- --      → isRecvMsg theStep
-- -- --      → CommittedValueWasSentBy2 post

-- -- --  cVSB2RecvMsg {pre} {post} preReach
-- -- --               theStep@(recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- -- --     with verifySigDirect {msg = msg} CommittedValueWasSentBy2 theStep isRecv (cVSB2Invariant preReach) rdy run≡
-- -- --  ...| inj₁ done = done pSt≡ max≡
-- -- --  ...| inj₂ (ver , R)
-- -- --     with peerOf theStep ≟ p
-- -- --  ...| no xx
-- -- --     -- A step of "by" does not affect the state of p ≢ by, and does not "unsend" messages
-- -- --     with cVSB2Invariant preReach (trans (sym (stepByOtherPreservesPeerState theStep xx)) pSt≡) max≡
-- -- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (msgs-stable theStep (m∈SM (msg1 preCons)))
-- -- --                                                           (msgs-stable theStep (m∈SM (msg2 preCons)))

-- -- --  cVSB2RecvMsg {pre} {post} preReach
-- -- --                        (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- -- --     | inj₂ (ver , R)
-- -- --     | yes refl
-- -- --     rewrite R
-- -- --     with lookup-correct-update-2 (maybe-⊥ rdy) pSt≡
-- -- --  ...| pSt≡ppost
-- -- -- --    with cong proj₁ run≡ | cong proj₂ (sym run≡)
-- -- --     with cong proj₁ (sym run≡) | cong proj₂ (sym run≡)
-- -- --  ...| ppost≡ | acts≡
-- -- --     with proj₁ (pureHandler msg ts ppre) ≟HR noChange
-- -- --  ...| yes hR≡noChange
-- -- --     with nothingNoEffect {ppre} {ppost} {msg} {ts} hR≡noChange ppost≡
-- -- --  ...| noEffect
-- -- --     with pSt≡ppost | sym noEffect
-- -- --  ...| refl | refl
-- -- --     with cVSB2Invariant preReach {pSt = ppre} {p = p} rdy max≡
-- -- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (∈SM-stable-list {msgs = actionsToSends ppre acts} (m∈SM (msg1 preCons)))
-- -- --                                                           (∈SM-stable-list {msgs = actionsToSends ppre acts} (m∈SM (msg2 preCons)))

-- -- --  cVSB2RecvMsg {pre} {post} preReach
-- -- --              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- -- --     | inj₂ (ver , R)
-- -- --     | yes refl
-- -- --     | pSt≡ppost
-- -- --     | ppost≡ | acts≡
-- -- --     | no hR≢noChange
-- -- --     rewrite R
-- -- --     with isGotFirstAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
-- -- --          isGotFirstAdvance (proj₁ (pureHandler msg ts ppre))
-- -- --  ...| just n | [ hR≡gFA ]
-- -- --     with gFAEffect {ppre} {ppost} {msg} {ts} {n} ppost≡ (isGotFirstAdvance≡ hR≡gFA)
-- -- --  ...| senderBecomesN , maxUnchanged
-- -- --     with (sym pSt≡ppost) | suc curMax ≟ :maxSeen ppre
-- -- --  ...| refl | no xx = ⊥-elim (xx (trans (sym max≡) maxUnchanged))
-- -- --  ...| refl | yes refl
-- -- --     with max≡
-- -- --  ...| refl
-- -- --     with cVSB2Invariant preReach {pSt = ppre} {p = p} rdy refl
-- -- --  ...| s1 , s2 , preCons = s1 , s2 , cVSB2ConsCast preCons (∈SM-stable-list {actionsToSends ppost acts} (m∈SM (msg1 preCons)))
-- -- --                                                           (∈SM-stable-list {actionsToSends ppost acts} (m∈SM (msg2 preCons)))
-- -- --  cVSB2RecvMsg {pre} {post} preReach
-- -- --              (recvMsg {direct msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy _) isRecv {pSt} {curMax} {p} pSt≡ max≡
-- -- --     | inj₂ (ver , R)
-- -- --     | yes refl
-- -- --     | pSt≡ppost
-- -- --     | ppost≡ | acts≡
-- -- --     | no hR≢noChange
-- -- --     | nothing | [ hR≢gFA ]
-- -- --     rewrite R
-- -- --     with isConfirmedAdvance (proj₁ (pureHandler msg ts ppre)) | inspect
-- -- --          isConfirmedAdvance (proj₁ (pureHandler msg ts ppre))
-- -- --  ...| nothing | [ hR≢cA ] = ⊥-elim (hR≢noChange (handlerResultIsSomething {proj₁ (pureHandler msg ts ppre)} hR≢cA hR≢gFA))
-- -- --  ...| just v' | [ hR≡cA ]
-- -- --     with  pSt≡ppost | cAEffect {ppre} {ppost} {msg} {ts} ppost≡ (isConfirmedAdvance≡ hR≡cA)
-- -- --  ...| refl | senderBecomesNothing , maxNew
-- -- --     with cACond {ppre} {msg} {ts} {v = v'} (isConfirmedAdvance≡ hR≡cA)
-- -- --  ...| msgVal≡v' , zzz , sender1 , xxx , diffSender
-- -- --     with :val msg ≟ v'
-- -- --  ...| no neq   = ⊥-elim (neq msgVal≡v')
-- -- --  ...| yes refl
-- -- --     with rVWSInvariant preReach {pSt = ppre} {curMax = :maxSeen ppre} sender1 p rdy xxx refl
-- -- --  ...| s1preCon
-- -- --     with suc-injective (trans (sym max≡) (trans maxNew zzz))
-- -- --  ...| refl = sender1
-- -- --            , :author msg
-- -- --            , (mkCVSB2Consequent
-- -- --                 diffSender
-- -- --                 (rVWSConsCast s1preCon (∈SM-stable-list {actionsToSends ppost acts} (m∈SM s1preCon)))
-- -- --                 (mkRVWSConsequent to msg ver
-- -- --                    (∈SM-stable-list {actionsToSends ppost acts } ∈SM-pre)
-- -- --                    refl
-- -- --                    (trans (sym maxNew) max≡)))

-- -- --  cVSB2RecvMsg {pre} {post} preReach
-- -- --               theStep@(recvMsg {gossip msg} {to} {ppre} {ppost} {acts} by ts ∈SM-pre rdy run≡) isRecv
-- -- --     with verifySigGossip {msg = msg} CommittedValueWasSentBy2 theStep isRecv (cVSB2Invariant preReach) rdy run≡
-- -- --  ...| inj₁ done = done
-- -- --  ...| inj₂ (ver' , R') = cVSB2RecvMsg {pre} {post} preReach theStep isRecv

-- -- --  cVSB2Invariant init {p = p} x = ⊥-elim (maybe-⊥ x kvm-empty)
-- -- --  cVSB2Invariant (step preReach (cheat by ts to m dis))  = cVSB2Cheat preReach (cheat by ts to m dis) tt
-- -- --  cVSB2Invariant (step preReach (initPeer by ts cI rdy)) = cVSB2InitPeer preReach (initPeer by ts cI rdy) tt
-- -- --  cVSB2Invariant (step preReach (recvMsg by ts ∈SM-pre ready trans)) = cVSB2RecvMsg preReach (recvMsg by ts ∈SM-pre ready trans) tt
