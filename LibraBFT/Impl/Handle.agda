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
open import LibraBFT.Impl.OBM.Rust.RustTypes
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

postulate -- TODO-2: define BootstrapInfo to match implementation and write these functions
  fakeInitVV  : BootstrapInfo → ValidatorVerifier

fakeInitSR : SafetyRules
fakeInitSR =
  let sr = fakeRM ^∙ lSafetyRules
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound ∙~ 0
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdEpoch          ∙~ 1
      sr = sr & srPersistentStorage ∙ pssSafetyData ∙ sdLastVote       ∙~ nothing
  in sr

fakeInitPG : ProposalGenerator
fakeInitPG = ProposalGenerator∙new 0

postulate -- TODO-1: fakeInitPE, fakeInitBS, fakeInitRS
  fakeInitPE : ProposerElection
  fakeInitBS : BlockStore
  fakeInitRS : RoundState

fakeInitRM : RoundManager
fakeInitRM = RoundManager∙new
           ObmNeedFetch∙new
           (EpochState∙new 1 (fakeInitVV fakeBootstrapInfo))
           fakeInitBS fakeInitRS fakeInitPE fakeInitPG fakeInitSR false

-- Eventually, the initialization should establish properties we care about.
-- For now we just initialise to fakeRM.
-- That means we cannot prove the base case for various properties,
-- e.g., in Impl.Properties.VotesOnce
-- TODO: create real RoundManager using LibraBFT.Impl.IO.OBM.Start
fakeInitialRoundManagerAndMessages
  : (a : Author) → BootstrapInfo
  → RoundManager × List NetworkMsg
fakeInitialRoundManagerAndMessages a _ = fakeInitRM , []

-- TODO-2: These "wrappers" can probably be shared with FakeImpl, and therefore more of this could
-- be factored into LibraBFT.ImplShared.Interface.* (maybe Output, in which case maybe that should
-- be renamed?)

fakeInitWrapper : NodeId → BootstrapInfo → RoundManager × List (LYT.Action NetworkMsg)
fakeInitWrapper nid g = ×-map₂ (List-map LYT.send) (fakeInitialRoundManagerAndMessages nid g)

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

fakeInitAndHandlers : SystemInitAndHandlers ℓ-RoundManager ConcSysParms
fakeInitAndHandlers = mkSysInitAndHandlers
                    fakeBootstrapInfo
                    fakeInitRM
                    (λ pid bootstrapInfo → just (fakeInitWrapper pid bootstrapInfo))
                    peerStep

------------------------------------------------------------------------------
-- real initialization

postulate
  now           : Instant
  pg            : ProposalGenerator

initEMWithOutput' : Either ErrLog (EpochManager × List Output)
initEMWithOutput' = do
  (nf , _ , vss , vv , pe , liws) ← GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
  let nfLiwsVssVvPe               = (nf , liws , vss , vv , pe)
      me                          = 0
  Init.initialize me nfLiwsVssVvPe now ObmNeedFetch∙new pg

initEMWithOutput : EitherD ErrLog (EpochManager × List Output)
initEMWithOutput = do
  (nf , _ , vss , vv , pe , liws) ← fromEither $ GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
  let nfLiwsVssVvPe               = (nf , liws , vss , vv , pe)
      me                          = 0
  fromEither $ Init.initialize me nfLiwsVssVvPe now ObmNeedFetch∙new pg

initEMWithOutput≡ : ∀ {x} → EitherD-run initEMWithOutput ≡ x → initEMWithOutput' ≡ x
initEMWithOutput≡ iewo
  with GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
... | Left err rewrite iewo = refl
... | Right (nf , _ , vss , vv , pe , liws)
  with Init.initialize 0 (nf , liws , vss , vv , pe) now ObmNeedFetch∙new pg
... | Left err rewrite iewo = refl
... | Right y  rewrite iewo = refl

initEMWithOutput≡' : ∀ {x} → initEMWithOutput' ≡ x → EitherD-run initEMWithOutput ≡ x
initEMWithOutput≡' iewo
  with GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
... | Left err rewrite iewo = refl
... | Right (nf , _ , vss , vv , pe , liws)
  with Init.initialize 0 (nf , liws , vss , vv , pe) now ObmNeedFetch∙new pg
... | Left err rewrite iewo = refl
... | Right y rewrite iewo = refl

------------------------------------------------------------------------------
-- TODO : ASK CHRIS : regarding EitherD-run

zzz : EitherD ErrLog ℕ
zzz = do
  r ← RightD 0
  RightD r

zzz' : Either ErrLog ℕ
zzz' = Right 0

zzz≡zzz' : zzz ≡ RightD 0 → zzz' ≡ Right 0
zzz≡zzz' ()
