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
open import LibraBFT.Impl.Util.Util
open import Optics.All

-- This module provides some scaffolding to define the handlers for our fake/simple
-- "implementation" and connect them to the interface of the SystemModel.

module LibraBFT.Impl.Handle
  (hash    : BitString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where
 open import LibraBFT.Impl.Consensus.RoundManager hash hash-cr
 open RWST-do

 open EpochConfig

 record GenesisInfo : Set where
   constructor mkGenInfo
   field
     -- Nodes, PKs for initial epoch
     -- Faults to tolerate (or quorum size?)
     genQC      : QuorumCert            -- We use the same genesis QC for both highestQC and
                                        -- highestCommitCert.

 postulate -- valid assumption
   -- We postulate the existence of GenesisInfo known to all
   genInfo : GenesisInfo

 postulate -- TODO-1: reasonable assumption that some RoundManager exists, though we could prove
           -- it by construction; eventually we will construct an entire RoundManagerAndMeta, so
           -- this won't be needed

 -- This represents an uninitialised RoundManager, about which we know nothing, which we use as
 -- the initial RoundManager for every peer until it is initialised.
   fakeRM : RoundManager

 postulate -- TODO-2: define GenesisInfo to match implementation and write these functions
   initVV  : GenesisInfo → ValidatorVerifier
   init-EC : GenesisInfo → EpochConfig

 initSR : SafetyRules
 initSR =  over (srPersistentStorage ∙ pssSafetyData ∙ sdEpoch) (const 1)
                (over (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound) (const 0)
                      (₋rmSafetyRules (₋rmEC fakeRM)))

 initRMEC : RoundManagerEC
 initRMEC = RoundManagerEC∙new initSR (initVV genInfo)

 postulate -- TODO-2 : prove these once initRMEC is defined directly
   init-EC-epoch-1  : epoch (init-EC genInfo) ≡ 1
   initRMEC-correct : RoundManagerEC-correct initRMEC

 initRM : RoundManager
 initRM = fakeRM

 -- Eventually, the initialization should establish some properties we care about, but for now we
 -- just initialise again to fakeRM, which means we cannot prove the base case for various
 -- properties, e.g., in Impl.Properties.VotesOnce
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

 -- Translation to SystemModel
 import LibraBFT.Yasm.Types as LYT
 -- For now, the SystemModel supports only one kind of action: to send a Message.  Later it might
 -- include things like logging, crashes, assertion failures, etc.
 initialRoundManagerAndMessagesWrapper : NodeId → GenesisInfo → RoundManager × List (LYT.Action NetworkMsg)
 initialRoundManagerAndMessagesWrapper nid g = ×-map₂ (List-map LYT.send) (initialRoundManagerAndMessages nid g)

 -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
 -- it is included in the model only to facilitate future work on liveness properties, when we will need
 -- assumptions about message delivery between honest peers.
 outputToActions : RoundManager → Output → List (LYT.Action NetworkMsg)
 outputToActions rm (BroadcastProposal p) = List-map (const (LYT.send (P p)))
                                              (kvm-toList (:vvAddressToValidatorInfo (₋rmValidators (₋rmEC rm))))
 outputToActions rm (LogErr _) = []
 outputToActions rm (SendVote v toList) = List-map (const (LYT.send (V v))) toList

 outputsToActions : (rm : RoundManager) → List Output → List (LYT.Action NetworkMsg)
 outputsToActions rm = concat ∘ List-map (outputToActions rm)

 runHandler : RoundManager → LBFT Unit → RoundManager × List (LYT.Action NetworkMsg)
 runHandler st handler = ×-map₂ (outputsToActions st) (proj₂ (LBFT-run handler st))

 peerStep : NodeId → NetworkMsg → Instant → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
 peerStep nid msg ts st = runHandler st (handle nid msg ts)

 peerStepWrapper : NodeId → NetworkMsg → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
 peerStepWrapper nid msg st = peerStep nid msg 0 st
