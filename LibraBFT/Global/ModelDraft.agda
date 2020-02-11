{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Abstract.BFT
open import LibraBFT.Concrete.Network as NM
open import LibraBFT.Global.Network
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Consensus.Types

open import Level

module LibraBFT.Global.ModelDraft
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 -- TODO: more temporary scaffolding
 postulate
   commandType : Set
   pki         : PKI
   instance
     encCmd : Encoder commandType

 open import LibraBFT.Concrete.EventProcessor hash hash-cr pki commandType
 open import LibraBFT.Concrete.Records

 NtwkMsg : Set
 NtwkMsg = NetworkMsg commandType

 open        LibraBFT.Global.Network.WithMsgType NtwkMsg

 record SystemState (a : Set) : Set where
   constructor sysState
   field
     sentMessages    : SentMessages
     eventProcessors : PK → EventProcessor a
 open SystemState

 initState : SystemState commandType
 initState = sysState noMessages initEventProcessor

 -- TODO: create an event where any NodeID can send a vote in its current epoch with a higher round than last voted round
 --       create an event where any node that is not an honest author for an epoch can send an arbitrary vote for that epoch
 --       dishonest one knows it's dishonest, so it could prov

 postulate
   fakeUID : Set   -- This is ugly, necessitated by overly specific definition of lemmab1
   _≟fakeUID_ : (u₀ u₁ : fakeUID) → Dec (u₀ ≡ u₁)

 data EventInitiator : EpochId → NodeId → Set where
   goodAuthor : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId                                                  → EventInitiator eId nId
   notAuthor  : ∀       (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ nothing                                                   → EventInitiator eId nId
   badAuthor  : ∀ {aId} (eId : EpochId) → (nId : NodeId) → isAuthor (fakeEC eId) nId ≡ just aId → ¬ (Honest (fakeEC eId) fakeUID _≟fakeUID_ aId) → EventInitiator eId nId


 data Enabled : ∀ {eId} {nId} → SystemState commandType → EventInitiator eId nId → Set where
   spontaneous : ∀ {ps : SystemState commandType}{eId}{nId} → (e : EventInitiator eId nId)                                        → Enabled ps e
   recvMessage : ∀ {ps : SystemState commandType}{eId}{nId}{e : EventInitiator eId nId} → (n : NtwkMsg) → n ∈SM (sentMessages ps) → Enabled ps e
   -- TODO: TIMEOUT (maybe model as special NetworkRecord?)

 -- MSM: the following is bogus and cannot exist in reality, it's just for making progress before
 -- thinking about how to model secret keys in practice
 postulate
   fakeKeyPair : (pk : PK) → ∃[ sk ](IsKeyPair pk sk)

 -- TODO: update this fake stuff to integrate handlers (see LibraBFT.Concrete.Handle)

 Step : ∀ {ps : SystemState commandType}{eId}{nId} → (e : EventInitiator eId nId) → Enabled ps e → SystemState commandType
 -- A fake action that spontaneously "broadcasts" a commit message.
 -- Currently it broadcasts the same commit every time, so no problem.  Later I want to make it so dishonest authors
 -- can send commits that break the rules but honest ones can't.
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (spontaneous e) = {!!}
{-   let cm  = mkCommitMsg eId nId 0 dummyHash
       scm = signed cm (sign (encode cm) (proj₁ (fakeKeyPair (pubKeyForNode nId))))
   in record ps { sentMessages = sendMsg (sentMessages ps) (wire Broadcast (C scm)) }
-}
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (recvMessage _ _) = ps
 Step {ps} (notAuthor  eId nId notAuth)           enab = ps
 Step {ps} (badAuthor  eId nId isAuth notHonest)  enab = ps

 data ReachableSystemState : SystemState commandType → Set where
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

  -- MSM: Note that we assume messages can be reordered and/or duplicated and/or dropped.  If we
  -- apply this also to CommitMsgs, then a client cannot rely on them being received in order, even
  -- if they are sent in order. Therefore the correctness condition says only that CommitMsgs
  -- sent by honest participants are consistent with each other.

  Correctness : ∀ {ss : SystemState commandType} {c₁ c₂ : CommitMsg} {α₁ α₂}
              → ReachableSystemState ss
              → (C c₁) ∈SM (sentMessages ss)
              → (C c₂) ∈SM (sentMessages ss)
              → is-just (check-signature (pkAuthor pki (cAuthor c₁)) c₁) ≡ true
              → is-just (check-signature (pkAuthor pki (cAuthor c₂)) c₂) ≡ true
              → isAuthor (fakeEC (cEpochId c₁)) (cAuthor c₁) ≡ just α₁
              → isAuthor (fakeEC (cEpochId c₂)) (cAuthor c₂) ≡ just α₂
              → Honest (fakeEC (cEpochId c₁)) fakeUID _≟fakeUID_ α₁
              → Honest (fakeEC (cEpochId c₂)) fakeUID _≟fakeUID_ α₂
              → cEpochId c₁ ≡ cEpochId c₂
              → cRound   c₁ ≡ cRound   c₂
                ---------------------
              → cCert  c₁ ≡ cCert  c₂
  Correctness = {!!}
