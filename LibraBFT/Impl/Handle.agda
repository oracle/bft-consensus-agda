{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.Liveness.RoundState as RoundState
import      LibraBFT.Impl.IO.OBM.GenKeyFile             as GenKeyFile
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
import      LibraBFT.Impl.OBM.Init                      as Init
open import LibraBFT.Impl.OBM.Time
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.Base
import      LibraBFT.Yasm.Types as LYT
open import Optics.All

-- This module provides scaffolding to define the handlers for our implementation model and connect
-- them to the interface of the SystemModel.  Initially it inherits a bunch of postulated stuff for
-- initial state from the fake implementation, but these will evolve here, while the fake one
-- probably won't.  There is probably more refactoring we can do with FakeImpl too (see comment
-- below).

module LibraBFT.Impl.Handle where

open EpochConfig

postulate -- TODO-1: reasonable assumption that some RoundManager exists, though we could prove
          -- it by construction; eventually we will construct an entire RoundManager, so
          -- this won't be needed

  -- This represents an uninitialised RoundManager, about which we know nothing, which we use as
  -- the initial RoundManager for every peer until it is initialised.
  fakeRM : RoundManager

postulate -- TODO-2: define GenesisInfo to match implementation and write these functions
  initVV  : GenesisInfo → ValidatorVerifier

initSR : SafetyRules
initSR =
  let sr = fakeRM ^∙ lSafetyRules
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound ∙~ 0
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdEpoch          ∙~ 1
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVote       ∙~ nothing
  in sr

initPG : ProposalGenerator
initPG = ProposalGenerator∙new 0

postulate -- TODO-1: initPE, initBS, initRS
  initPE : ProposerElection
  initBS : BlockStore
  initRS : RoundState

initRM : RoundManager
initRM = RoundManager∙new
           ObmNeedFetch∙new
           (EpochState∙new 1 (initVV genesisInfo))
           initBS initRS initPE initPG initSR false

postulate
  now           : Instant
  pg            : ProposalGenerator

initEMWithOutput : Either ErrLog (EpochManager × List Output)
initEMWithOutput = do
  (nf , _ , vss , vv , pe , liws) ← GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
  let nfLiwsVssVvPe               = (nf , liws , vss , vv , pe)
      me                          = 0
  Init.initialize me nfLiwsVssVvPe now ObmNeedFetch∙new pg

initRMWithOutput : Either ErrLog (RoundManager × List Output)
initRMWithOutput = do
  (em , out) ← initEMWithOutput
  rm         ← em ^∙ emObmRoundManager
  pure (rm , out)

initRM' : Either ErrLog RoundManager
initRM' = fst <$> initRMWithOutput

-- Eventually, the initialization should establish properties we care about.
-- For now we just initialise to fakeRM.
-- That means we cannot prove the base case for various properties,
-- e.g., in Impl.Properties.VotesOnce
-- TODO: create real RoundManager using LibraBFT.Impl.IO.OBM.Start
initialRoundManagerAndMessages
  : (a : Author) → GenesisInfo
  → RoundManager × List NetworkMsg
initialRoundManagerAndMessages a _ = initRM , []

-- TODO-2: These "wrappers" can probably be shared with FakeImpl, and therefore more of this could
-- be factored into LibraBFT.ImplShared.Interface.* (maybe Output, in which case maybe that should
-- be renamed?)

initWrapper : NodeId → GenesisInfo → RoundManager × List (LYT.Action NetworkMsg)
initWrapper nid g = ×-map₂ (List-map LYT.send) (initialRoundManagerAndMessages nid g)

-- Here we invoke the handler that models the real implementation handler.
runHandler : RoundManager → LBFT Unit → RoundManager × List (LYT.Action NetworkMsg)
runHandler st handler = ×-map₂ (outputsToActions {st}) (proj₂ (LBFT-run handler st))

-- And ultimately, the all-knowing system layer only cares about the
-- step function.
--
-- Note that we currently do not do anything non-trivial with the timestamp.
-- Here, we just pass 0 to `handle`.
peerStep : NodeId → NetworkMsg → RoundManager → RoundManager × List (LYT.Action NetworkMsg)
peerStep nid msg st = runHandler st (handle nid msg 0)

InitAndHandlers : SystemInitAndHandlers ℓ-RoundManager ConcSysParms
InitAndHandlers = mkSysInitAndHandlers
                    genesisInfo
                    initRM
                    initWrapper
                    peerStep

