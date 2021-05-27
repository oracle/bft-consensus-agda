{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import Optics.All

-- This module provides some scaffolding to define the handlers for our fake/simple
-- "implementation" and connect them to the interface of the SystemModel.

module LibraBFT.Impl.Handle where
 open import LibraBFT.Impl.Consensus.RoundManager
 open RWST-do

 open EpochConfig

 record GenesisInfo : Set where
   constructor mkGenInfo
   field
     -- TODO-1 : Nodes, PKs for initial epoch
     -- TODO-1 : Faults to tolerate (or quorum size?)
     genQC      : QuorumCert            -- We use the same genesis QC for both highestQC and
                                        -- highestCommitCert.
 open GenesisInfo

 postulate -- valid assumption
   -- We postulate the existence of GenesisInfo known to all
   -- TODO: construct one or write a function that generates one from some parameters.
   genInfo : GenesisInfo

 postulate -- TODO-2: define GenesisInfo to match implementation and write these functions
   initVV  : GenesisInfo → ValidatorVerifier
   init-EC : GenesisInfo → EpochConfig

 data ∈GenInfo : Signature → Set where
  inGenQC : ∀ {vs} → vs ∈ qcVotes (genQC genInfo) → ∈GenInfo (proj₂ vs)

 open import LibraBFT.Abstract.Records UID _≟UID_ NodeId
                                       (init-EC genInfo)
                                       (ConcreteVoteEvidence (init-EC genInfo))
                                       as Abs using ()

 postulate -- TODO-1 : prove
   ∈GenInfo? : (sig : Signature) → Dec (∈GenInfo sig)

 postulate -- TODO-1: prove after defining genInfo
   genVotesRound≡0     : ∀ {pk v}
                      → (wvs : WithVerSig pk v)
                      → ∈GenInfo (ver-signature wvs)
                      → v ^∙ vRound ≡ 0
   genVotesConsistent : (v1 v2 : Vote)
                      → ∈GenInfo (₋vSignature v1) → ∈GenInfo (₋vSignature v2)
                      → v1 ^∙ vProposedId ≡ v2 ^∙ vProposedId

 postulate -- TODO-1: reasonable assumption that some RoundManager exists, though we could prove
           -- it by construction; eventually we will construct an entire RoundManager, so
           -- this won't be needed

 -- This represents an uninitialised RoundManager, about which we know nothing, which we use as
 -- the initial RoundManager for every peer until it is initialised.
   fakeRM : RoundManager

 initSR : SafetyRules
 initSR =  over (srPersistentStorage ∙ pssSafetyData ∙ sdEpoch) (const 1)
                (over (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound) (const 0)
                      (₋rmSafetyRules (₋rmEC fakeRM)))

 initRMEC : RoundManagerEC
 initRMEC = RoundManagerEC∙new (EpochState∙new 1 (initVV genInfo)) initSR

 postulate -- TODO-2 : prove these once initRMEC is defined directly
   init-EC-epoch-1  : epoch (init-EC genInfo) ≡ 1
   initRMEC-correct : RoundManagerEC-correct initRMEC

 initRM : RoundManager
 initRM = fakeRM

 -- Eventually, the initialization should establish some properties we care about, but for now we
 -- just initialise again to fakeRM, which means we cannot prove the base case for various
 -- properties, e.g., in Impl.Properties.VotesOnce
 -- TODO: create real RoundManager using GenesisInfo
 initialRoundManagerAndMessages
     : (a : Author) → GenesisInfo
     → RoundManager × List NetworkMsg
 initialRoundManagerAndMessages a _ = initRM , []

 handle : NodeId → NetworkMsg → Instant → LBFT Unit
 handle _self msg now
    with msg
 ...| P p = processProposalMsg now p
 ...| V v = processVote now v
 ...| C c = return unit            -- We don't do anything with commit messages, they are just for defining Correctness.

 -- For now, the SystemModel supports only one kind of action: to send a Message.  Later it might
 -- include things like logging, crashes, assertion failures, etc.  At that point, definitions like
 -- the following might become part of the SystemModel, but they are included here to enable the
 -- temporary scaffolding below.

 data Action (Msg : Set) : Set where
   send : Msg → Action Msg

 action-send-injective : ∀ {Msg}{m m' : Msg} → send m ≡ send m' → m ≡ m'
 action-send-injective refl = refl

 msgToSend : {Msg : Set} → Action Msg → Msg
 msgToSend (send m) = m

 msgToSend≡ : ∀ {Msg x}{m : Msg} → m ≡ msgToSend x → send m ≡ x
 msgToSend≡ {_} {send m} {m} refl = refl

 -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
 -- it is included in the model only to facilitate future work on liveness properties, when we will need
 -- assumptions about message delivery between honest peers.
 outputToActions : RoundManager → Output → List (Action NetworkMsg)
 outputToActions rm (BroadcastProposal p) = List-map (const (Action.send (P p)))
                                                     (List-map proj₁
                                                               (kvm-toList (:vvAddressToValidatorInfo (₋esVerifier (₋rmEpochState (₋rmEC rm))))))
 outputToActions _  (LogErr x)            = []
 outputToActions _  (SendVote v toList)   = List-map (const (Action.send (V v))) toList

 outputsToActions : ∀ {State} → List Output → List (Action NetworkMsg)
 outputsToActions {st} = concat ∘ List-map (outputToActions st)

 runHandler : RoundManager → LBFT Unit → RoundManager × List (Action NetworkMsg)
 runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

 -- And ultimately, the all-knowing system layer only cares about the
 -- step function.
 peerStep : NodeId → NetworkMsg → Instant → RoundManager → RoundManager × List (Action NetworkMsg)
 peerStep nid msg ts st = runHandler st (handle nid msg ts)

 -- This (temporary) wrapper bridges the gap between our (draft) concrete handler and
 -- the form required by the new system model, which does not (yet) support actions other
 -- than send.
 peerStepWrapper : NodeId → NetworkMsg → RoundManager → RoundManager × List NetworkMsg
 peerStepWrapper nid msg st = ×-map₂ (List-map msgToSend) (peerStep nid msg 0 st)
