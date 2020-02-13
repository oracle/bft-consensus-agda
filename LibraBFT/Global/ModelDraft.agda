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
   pki         : NodeId → PK

 open import LibraBFT.Concrete.Handle
 open import LibraBFT.Concrete.Records
 open import LibraBFT.Concrete.BlockTree hash hash-cr

 -- TODO: this will eventually call processCertificatesM with genesis QC, similar to Haskell code
 initialEventProcessorAndMessages : Author → EventProcessor × List Action
 initialEventProcessorAndMessages = const (eventProcessor (fakeEC 0) (mkBlockStore (emptyBT (fakeEC 0))) [] , [])  -- TODO: real list of authors, other details

 actionsToSends : EventProcessor → Action → List (Author × NetworkMsg)
 actionsToSends ep (BroadcastProposal p) = List-map (_, (P p)) (epValidators ep)
 actionsToSends _  (LogErr x)            = []
 actionsToSends _  (SendVote v to)       = List-map (_, (V v)) to

 -- This captures whether the author can be counted amongst the dishonest authors of the releavnt
 -- epoch (identified by the message the author would like to send).  Thus, someone who is not an
 -- author of the epoch is not a dishonest author of the epoch.
 --
 -- TODO: For now we use fakeEC.  We will need to access "real" epoch configs somehow.  These will
 -- need to be created from concrete state when epoch configuration changes are committed.  It seems
 -- that a validator will need to know configuration for all epochs in order to validate authors of
 -- messages.  Where is this information held in the Rust/Haskell code?  In the real code, peers don't
 -- need details of epoch other than the one they're currently in, so they don't have sufficient
 -- information to construct and EpochConfig for other epochs.  So how can we model this?
 DishonestAuthor : NetworkMsg → Author → Set
 DishonestAuthor m a with (fakeEC (getEpoch m))
 ...| ec with isAuthor ec a
 ...| nothing = ⊥
 ...| just α  = ¬ (Honest ec α)

 open import LibraBFT.Global.SystemModel
               Instant
               Author
               NetworkMsg
               sig-NetworkMsg
               Unit
               Action
               EventProcessor
               initialEventProcessorAndMessages
               handle
               actionsToSends
               DishonestAuthor

 -- module _ (ec : EpochConfig) where

 --  -- For a given epoch, in any reachable state, if there are two verifibly signed commit messages
 --  -- from two honest authors of that epoch, each message is verified against the appropriate public
 --  -- key, and both are for the same round, then they both say to commit the same thing (commit
 --  -- certificate).

 --  -- MSM: Note that we assume messages can be reordered and/or duplicated and/or dropped.  If we
 --  -- apply this also to CommitMsgs, then a client cannot rely on them being received in order, even
 --  -- if they are sent in order. Therefore the correctness condition says only that CommitMsgs
 --  -- sent by honest participants are consistent with each other.

 --  Correctness : ∀ {ss : SystemState commandType} {c₁ c₂ : CommitMsg} {α₁ α₂}
 --              → ReachableSystemState ss
 --              → (C c₁) ∈SM (sentMessages ss)
 --              → (C c₂) ∈SM (sentMessages ss)
 --              → is-just (check-signature (pkAuthor pki (cAuthor c₁)) c₁) ≡ true
 --              → is-just (check-signature (pkAuthor pki (cAuthor c₂)) c₂) ≡ true
 --              → isAuthor (fakeEC (cEpochId c₁)) (cAuthor c₁) ≡ just α₁
 --              → isAuthor (fakeEC (cEpochId c₂)) (cAuthor c₂) ≡ just α₂
 --              → Honest (fakeEC (cEpochId c₁)) fakeUID _≟fakeUID_ α₁
 --              → Honest (fakeEC (cEpochId c₂)) fakeUID _≟fakeUID_ α₂
 --              → cEpochId c₁ ≡ cEpochId c₂
 --              → cRound   c₁ ≡ cRound   c₂
 --                ---------------------
 --              → cCert  c₁ ≡ cCert  c₂
 --  Correctness = {!!}
