{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}
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
import      LibraBFT.Yasm.Types as LYT
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

 initRS : RoundState
 initRS = RoundState∙new 0

 initSR : SafetyRules
 initSR =  over (srPersistentStorage ∙ pssSafetyData ∙ sdEpoch) (const 1)
                (over (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound) (const 0)
                      (₋rmSafetyRules (₋rmEC fakeRM)))

 -- TODO-1: Implement this.
 initPE : ProposerElection
 initPE = obm-dangerous-magic!

 initRMEC : RoundManagerEC
 initRMEC = RoundManagerEC∙new (EpochState∙new 1 (initVV genInfo)) initRS initPE initSR

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
 ...| P p = fakeProcessProposalMsg now p
 ...| V v = processVote now v
 ...| C c = return unit            -- We don't do anything with commit messages, they are just for defining Correctness.

 initWrapper : NodeId → GenesisInfo → RoundManager × List (LYT.Action NetworkMsg)
 initWrapper nid g = ×-map₂ (List-map LYT.send) (initialRoundManagerAndMessages nid g)

 -- Note: the SystemModel allows anyone to receive any message sent, so intended recipient is ignored;
 -- it is included in the model only to facilitate future work on liveness properties, when we will need
 -- assumptions about message delivery between honest peers.
 outputToActions : RoundManager → Output → List (LYT.Action NetworkMsg)
 outputToActions rm (BroadcastProposal p) = List-map (const (LYT.send (P p)))
                                                     (List-map proj₁
                                                               (kvm-toList (:vvAddressToValidatorInfo (₋esVerifier (₋rmEpochState (₋rmEC rm))))))
 outputToActions _  (LogErr x)            = []
 outputToActions _  (SendVote v toList)   = List-map (const (LYT.send (V v))) toList

 outputsToActions : ∀ {State} → List Output → List (LYT.Action NetworkMsg)
 outputsToActions {st} = concat ∘ List-map (outputToActions st)

 runHandler : RoundManager → LBFT Unit → RoundManager × List (LYT.Action NetworkMsg)
 runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

 -- And ultimately, the all-knowing system layer only cares about the
 -- step function.
 --
 -- Note that we currently do not do anything non-trivial with the timestamp.
 -- Here, we just pass 0 to `handle`.
 peerStep : NodeId → NetworkMsg → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
 peerStep nid msg st = runHandler st (handle nid msg 0)
