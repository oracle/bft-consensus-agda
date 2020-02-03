{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Abstract.BFT
open import LibraBFT.Concrete.Network as NM
open import LibraBFT.Global.Network
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Types

open import Level

module LibraBFT.Global.ModelDraft
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 postulate
   commandType : Set -- TODO: more temporary scaffolding
   pki         : PKI

 open import LibraBFT.Concrete.EventProcessor hash hash-cr pki commandType
 open import LibraBFT.Concrete.Records pki

 open        LibraBFT.Global.Network.WithMsgType 

 record SystemState : Set where
   constructor sysState
   field
     sentMessages    : SentMessages
     eventProcessors : PK → EventProcessor
 open SystemState

 initState : SystemState
 initState = sysState noMessages initEventProcessor

 -- TODO: create an event where any NodeID can send a vote in its current epoch with a higher round than last voted round
 --       create an event where any node that is not an honest author for an epoch can send an arbitrary vote for that epoch
 --       dishonest one knows it's dishonest, so it could prov

 postulate
   fakeUID : Set   -- This is ugly, necessitated by overly specific definition of lemmab1
   _≟fakeUID_ : (u₀ u₁ : fakeUID) → Dec (u₀ ≡ u₁)

 data EventInitiator : EpochId → NodeId → Set where
   goodAuthor : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId                               → EventInitiator eId nId
   notAuthor  : ∀       (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ nothing                                → EventInitiator eId nId
   badAuthor  : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId → ¬ (Honest (fakeEC eId) aId) → EventInitiator eId nId

 data Enabled : ∀ {eId} {nId} → SystemState → EventInitiator eId nId → Set where
   spontaneous : ∀ {ps : SystemState}{eId}{nId} → (e : EventInitiator eId nId)                                              → Enabled ps e
   recvMessage : ∀ {ps : SystemState}{eId}{nId}{e : EventInitiator eId nId} → (n : NetworkMsg) → n ∈SM (sentMessages ps) → Enabled ps e
   -- TODO: TIMEOUT (maybe model as special NetworkRecord?)

 -- MSM: the following is bogus and cannot exist in reality, it's just for making progress before
 -- thinking about how to model secret keys in practice
 postulate
   fakeKeyPair : (pk : PK) → ∃[ sk ](IsKeyPair pk sk)

 Step : ∀ {ps : SystemState}{eId}{nId} → (e : EventInitiator eId nId) → Enabled ps e → SystemState
 -- A fake action that spontaneously "broadcasts" a commit message.
 -- Currently it broadcasts the same commit every time, so no problem.  Later I want to make it so dishonest authors
 -- can send commits that break the rules but honest ones can't.
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (spontaneous e) = ?
{-   let cm  = mkCommitMsg eId nId 0 dummyHash
       scm = signed cm (sign (encode cm) (proj₁ (fakeKeyPair (pubKeyForNode nId))))
   in record ps { sentMessages = sendMsg (sentMessages ps) (wire Broadcast (C scm)) }
-}
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (recvMessage _ _) = ps
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

 module _ (ec : EpochConfig) where

  -- For a given epoch, in any reachable state, if there are two verifibly signed commit messages
  -- from two honest authors of that epoch, each message is verified against the appropriate public
  -- key, and both are for the same round, then they both say to commit the same thing (commit
  -- certificate).

  Correctness : ∀ {ss : SystemState} {c₁} {c₂} {eId : EpochId} {α₁} {α₂}
              → ReachableSystemState ss
              → c₁ ∈SM (sentMessages ss)
              → c₂ ∈SM (sentMessages ss)
              → {vs₁ : VerSigned Commit}
              → {vs₂ : VerSigned Commit}
              → {pk₁ : verWithPK vs₁ ≡ pubKeyForNode (getAuthor vs₁)}
              → {pk₂ : verWithPK vs₂ ≡ pubKeyForNode (getAuthor vs₂)}
              → check-signature-and-format (content c₁) ≡ just (C vs₁ pk₁)
              → check-signature-and-format (content c₂) ≡ just (C vs₂ pk₂)
              → getEpochId vs₁ ≡ eId
              → getEpochId vs₂ ≡ eId
              → isAuthor (fakeEC eId) (getAuthor vs₁) ≡ just α₁
              → isAuthor (fakeEC eId) (getAuthor vs₂) ≡ just α₂
              → Honest (fakeEC (getEpochId vs₁)) α₁
              → Honest (fakeEC (getEpochId vs₂)) α₂
              → getRound vs₁ ≡ getRound vs₂
              → getPrevHash vs₁ ≡ getPrevHash vs₂
  Correctness = {!!}
