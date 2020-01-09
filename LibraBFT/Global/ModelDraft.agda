{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude hiding (_⊔_)
open import LibraBFT.Abstract.BFT
open import LibraBFT.Concrete.RecordStoreState using (RecordStoreState ; emptyRSS)
open import LibraBFT.Concrete.NetworkMessages
open import LibraBFT.Global.Network
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.Types
open import LibraBFT.Global.Network
open        WithMsgType NetworkMsg


open import Level

module LibraBFT.Global.ModelDraft
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

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
 initState = sysState noMessages (λ _ → initNodeState)

 -- TODO: create an event where any NodeID can send a vote in its current epoch with a higher round than last voted round
 --       create an event where any node that is not an honest author for an epoch can send an arbitrary vote for that epoch
 --       dishonest one knows it's dishonest, so it could prov

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
 -- A fake action that spontaneously "broadcasts" a vote message.
 -- Currently it broadcasts the same vote every time, so no problem.  Later I want to make it so dishonest authors
 -- can send votes that break the rules but honest ones can't.
 Step {ps}{eId} {nId} (goodAuthor {aId} eId nId isAuth) (spontaneous e) =
   let vote  = mkVote eId nId dummyHash 0 0
       sVote = signed vote (sign (encode vote) (proj₁ (fakeKeyPair (pkAuthor (fakeEC eId) aId))))
   in record ps { sentMessages = sendMsg (sentMessages ps) (wire Broadcast (V sVote)) }
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

  open import LibraBFT.Abstract.Records ec

  -- For a given epoch, in any reachable state, if there are two verifibly signed commit messages
  -- from two honest authors of that epoch, each message is verified against the appropriate public
  -- key, and both are for the same round, then they both say to commit the same thing (commit
  -- certificate).

  Correctness : ∀ {ss : SystemState} {c₁} {c₂}
              → ReachableSystemState ss
              → c₁ ∈SM (sentMessages ss)
              → c₂ ∈SM (sentMessages ss)
              → {vs₁ : VerSigned (BC (Author ec)) ⦃ encA = encBC ⦃ encA = encAuthors ⦄ ⦄ }
              → {vs₂ : VerSigned (BC (Author ec)) ⦃ encA = encBC ⦃ encA = encAuthors ⦄ ⦄ }
              → Honest ec (getAuthor vs₁)
              → Honest ec (getAuthor vs₂)
              → {pk₁ : verWithPK vs₁ ≡ (pkAuthor ec (getAuthor vs₁))}
              → {pk₂ : verWithPK vs₂ ≡ (pkAuthor ec (getAuthor vs₂))}
              → check-signature-and-format ec (content c₁) ≡ just (C vs₁ pk₁)
              → check-signature-and-format ec (content c₂) ≡ just (C vs₂ pk₂)
              → getRound vs₁ ≡ getRound vs₂
              → cCert (content vs₁) ≡ cCert (content vs₂)
  Correctness = {!!}
