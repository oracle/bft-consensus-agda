{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import Optics.All
open import Util.KVMap                           as Map
open import Util.PKCS
open import Util.Prelude

module LibraBFT.Impl.Consensus.EpochManagerTypes where

------------------------------------------------------------------------------
-- in Haskell, this lives in LBFT.Consensus.Types
-- It lives here because of the dependency on RoundManager.

data RoundProcessor : Set where
  RoundProcessorRecovery : RecoveryManager → RoundProcessor
  RoundProcessorNormal   : RoundManager    → RoundProcessor

record EpochManager : Set where
  constructor mkEpochManager
  field
    _emAuthor             : Author
    _emConfig             : ConsensusConfig
    _emStateComputer      : StateComputer
    _emStorage            : PersistentLivenessStorage
    _emSafetyRulesManager : SafetyRulesManager
    _emProcessor          : Maybe RoundProcessor
open EpochManager public
unquoteDecl emAuthor   emConfig   emStateComputer   emStorage   emSafetyRulesManager   emProcessor = mkLens (quote EpochManager)
           (emAuthor ∷ emConfig ∷ emStateComputer ∷ emStorage ∷ emSafetyRulesManager ∷ emProcessor ∷ [])

-- getter only in Haskell
emEpochState : Lens EpochManager (Either ErrLog EpochState)
emEpochState = mkLens' g s
 where
  g : EpochManager → Either ErrLog EpochState
  g em = case em ^∙ emProcessor of λ where
           (just (RoundProcessorNormal   p)) → pure (p ^∙ rmEpochState)
           (just (RoundProcessorRecovery p)) → pure (p ^∙ rcmEpochState)
           nothing                           → Left fakeErr
  s : EpochManager → Either ErrLog EpochState → EpochManager
  s em _ = em

-- getter only in Haskell
emEpoch : Lens EpochManager (Either ErrLog Epoch)
emEpoch = mkLens' g s
 where
  g : EpochManager → Either ErrLog Epoch
  g em = (_^∙ esEpoch) <$> (em ^∙ emEpochState)
  s : EpochManager → Either ErrLog Epoch → EpochManager
  s em _ = em

-- getter only in Haskell
emObmRoundManager : Lens EpochManager (Either ErrLog RoundManager)
emObmRoundManager = mkLens' g s
 where
  g : EpochManager → Either ErrLog RoundManager
  g em = case em ^∙ emProcessor of λ where
           (just (RoundProcessorNormal rm))  → pure rm
           (just (RoundProcessorRecovery _)) → Left fakeErr
           nothing                           → Left fakeErr
  s : EpochManager → Either ErrLog RoundManager -> EpochManager
  s em _ = em
