{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Abstract.BFT
open import LibraBFT.Concrete.Network
open import LibraBFT.Concrete.RecordStoreState using (RecordStoreState ; emptyRSS)
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.Types

open import Level

module LibraBFT.Global.ModelDraft
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where
{-
VCM:

 I think the global state should be something like:

 > record SystemState : Set where
 >   constructor sysState
 >   field
 >     msgQueue   : List (Σ NetworkMsg SentByBlaBlaBla)
 >     nodeStates : NodeId → NodeState

 and the events should be something like:

 a. step node, which pops a message addressed to node x
 and calls the handle function; take the post state to be
 the result of the handle function and append the necessary outgoing
 messages.

 b. drop message, which forgets a message

 ...

 It seems like network layer assumptions do really only show up here,
 which is good.

-}

 -- VCM: Why not List NetworkRecord? Plus, we will need 
 -- destination and assumptions on the network layer still.
 data SentMessages : Set where
   empty : SentMessages
   send  : SentMessages → NetworkRecord → SentMessages

 data _∈SM_ : NetworkRecord → SentMessages → Set where

 record NodeState : Set where
   constructor nodeState
   field
     currentEpoch   : EpochConfig
     lastVotedRound : Round
     rss            : RecordStoreState hash hash-cr currentEpoch

 initNodeState : NodeState
 initNodeState = nodeState (fakeEC 0) 0 (emptyRSS hash hash-cr (fakeEC 0))


 record SystemState : Set where
   constructor sysState
   field
     sentMessages : SentMessages
     nodeStates   : NodeId → NodeState
 open SystemState

 initState : SystemState
 initState = sysState empty (λ _ → initNodeState)

 -- TODO: create an event where any NodeID can send a vote in its current epoch with a higher round than last voted round
 --       create an event where any node that is not an honest author for an epoch can send an arbitrary vote for that epoch
 --       dishonest one knows it's dishonest, so it could prov

 -- VCM: I don't understand why these are "events". Do they transition
 -- the state of the system? I should read the paper where this formalism is
 -- introduced before deepening my confusion.
 data EventInitiator : EpochId → NodeId → Set where
   goodAuthor : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId                               → EventInitiator eId nId
   notAuthor  : ∀       (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ nothing                                → EventInitiator eId nId
   badAuthor  : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId → ¬ (Honest (fakeEC eId) aId) → EventInitiator eId nId

 data Enabled : ∀ {eId} {nId} → SystemState → EventInitiator eId nId → Set where
   spontaneous : ∀ {ps : SystemState}{eId}{nId} → (e : EventInitiator eId nId)                                              → Enabled ps e
   recvMessage : ∀ {ps : SystemState}{eId}{nId}{e : EventInitiator eId nId} → (n : NetworkRecord) → n ∈SM (sentMessages ps) → Enabled ps e
   -- TODO: TIMEOUT (maybe model as special NetworkRecord?)

 -- MSM: the following is bogus and cannot exist in reality, it's just for making progress before
 -- thinking about how to model secret keys in practice
 postulate
   fakeKeyPair : (pk : PK) → ∃[ sk ](IsKeyPair pk sk)

 Step : ∀ {ps : SystemState}{eId}{nId} → (e : EventInitiator eId nId) → Enabled ps e → SystemState
 -- A fake action that spontaneously "sends" a vote message.
 -- Currently it sends the same vote every time, so no problem.  Later I want to make it so dishonest authors
 -- can send votes that break the rules but honest ones can't.
 -- MSM: why don't I get a "missing cases" warning here, if there is no recvMessage case?
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (spontaneous e) =
   let vote  = mkVote eId nId dummyHash 0 0
       sVote = signed vote (sign (encode vote) (proj₁ (fakeKeyPair (pkAuthor (fakeEC eId) aId))))
   in record ps { sentMessages = send (sentMessages ps) (V sVote) }
 Step {ps} (notAuthor  eId nId notAuth)           enab = ps
 Step {ps} (badAuthor  eId nId isAuth notHonest)  enab = ps

 data ReachableSystemState : SystemState → Set where
   init : ReachableSystemState initState
   step : ∀ {preState postState} {eId} {nId}
        → ReachableSystemState preState
        → {e : EventInitiator eId nId}
        → {en : Enabled preState e}
        → Step {preState} {eId} {nId} e en ≡ postState
        → ReachableSystemState postState


 -- If two commit messages are sent by two honest authors of the same epoch at the same round, then
 -- their contents (which will probably change) are the same.

 module _ (ec : EpochConfig) where

  open import LibraBFT.Abstract.Records ec

  -- In any reachable state, for a given epoch, if there are two verifibly signed commit messages
  -- from two honest authors of that epoch, and both are for the same round, then they both say to
  -- commit the same thing (commit certificate).

  Correctness : ∀ {α₁ α₂} {ss : SystemState} {aId₁} {aId₂}
              → ReachableSystemState ss
              → isAuthor ec α₁ ≡ just aId₁ → Honest ec aId₁
              → isAuthor ec α₂ ≡ just aId₂ → Honest ec aId₂
              → {c₁ : NetworkRecord}
              → {c₂ : NetworkRecord}
              → c₁ ∈SM (sentMessages ss)
              → c₂ ∈SM (sentMessages ss)
              → {vs₁ : VerSigned (BC (Author ec)) ⦃ encA = encBC ⦃ encA = encAuthors ⦄ ⦄ }
              → {vs₂ : VerSigned (BC (Author ec)) ⦃ encA = encBC ⦃ encA = encAuthors ⦄ ⦄ }
              → {pk₁ : verWithPK vs₁ ≡ (pkAuthor ec (getAuthor vs₁))}
              → {pk₂ : verWithPK vs₂ ≡ (pkAuthor ec (getAuthor vs₂))}
              → check-signature-and-format ec c₁ ≡ just (C vs₁ pk₁)
              → check-signature-and-format ec c₂ ≡ just (C vs₂ pk₂)
              → getRound vs₁ ≡ getRound vs₂
              → cCert (content vs₁) ≡ cCert (content vs₂)
  Correctness = {!!}
