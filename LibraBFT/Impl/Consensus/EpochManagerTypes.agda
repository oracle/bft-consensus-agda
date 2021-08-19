{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                  as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                          as String

module LibraBFT.Impl.Consensus.EpochManagerTypes where

------------------------------------------------------------------------------

-- TODO-1 : These types will eventually go into the existing types modules

------------------------------------------------------------------------------
-- from LBFT.Consensus.Types

data ConsensusScheme : Set where mkConsensusScheme : ConsensusScheme
-- instance S.Serialize ConsensusScheme

record ValidatorSet : Set where
  constructor ValidatorSet∙new
  field
    _vsScheme  : ConsensusScheme
    _vsPayload : List ValidatorInfo
-- instance S.Serialize ValidatorSet

record OnChainConfigPayload : Set where
  constructor OnChainConfigPayload∙new
  field
    _occpEpoch           : Epoch
    _occpObmValidatorSet : ValidatorSet
open OnChainConfigPayload public
unquoteDecl occpEpoch   occpObmValidatorSet = mkLens (quote OnChainConfigPayload)
           (occpEpoch ∷ occpObmValidatorSet ∷ [])
-- instance S.Serialize OnChainConfigPayload

record ReconfigEventEpochChange : Set where
  constructor ReconfigEventEpochChange∙new
  field
    _reecOnChainConfigPayload : OnChainConfigPayload
-- instance S.Serialize ReconfigEventEpochChange

record EpochChangeProof : Set where
  constructor EpochChangeProof∙new
  field
    _ecpLedgerInfoWithSigs : List LedgerInfoWithSignatures
    _ecpMore               : Bool
open EpochChangeProof public
unquoteDecl ecpLedgerInfoWithSigs   ecpMore = mkLens (quote EpochChangeProof)
           (ecpLedgerInfoWithSigs ∷ ecpMore ∷ [])
-- instance S.Serialize EpochChangeProof

data SafetyRulesWrapper : Set where
  SRWLocal : SafetyRules → SafetyRulesWrapper

record SafetyRulesManager : Set where
  constructor mkSafetyRulesManager
  field
    _srmInternalSafetyRules : SafetyRulesWrapper
open SafetyRulesWrapper public
unquoteDecl srmInternalSafetyRules = mkLens  (quote SafetyRulesManager)
           (srmInternalSafetyRules ∷ [])

data SafetyRulesService : Set where
  SRSLocal : SafetyRulesService

record SafetyRulesConfig : Set where
  constructor SafetyRulesConfig∙new
  field
    _srcService                     : SafetyRulesService
    _srcExportConsensusKey          : Bool
    _srcObmGenesisWaypoint          : Waypoint
open SafetyRulesConfig public
unquoteDecl srcService   srcExportConsensusKey   srcObmGenesisWaypoint = mkLens  (quote SafetyRulesConfig)
           (srcService ∷ srcExportConsensusKey ∷ srcObmGenesisWaypoint ∷ [])

record ConsensusConfig : Set where
  constructor ConsensusConfig∙new
  field
    _ccMaxPrunedBlocksInMem  : Usize
    _ccRoundInitialTimeoutMS : U64
    _ccSafetyRules           : SafetyRulesConfig
    _ccSyncOnly              : Bool
open ConsensusConfig public
unquoteDecl ccMaxPrunedBlocksInMem   ccRoundInitialTimeoutMS   ccSafetyRules   ccSyncOnly = mkLens (quote ConsensusConfig)
           (ccMaxPrunedBlocksInMem ∷ ccRoundInitialTimeoutMS ∷ ccSafetyRules ∷ ccSyncOnly ∷ [])

record NodeConfig : Set where
  constructor NodeConfig∙new
  field
    _ncObmMe     : AuthorName
    _ncConsensus : ConsensusConfig
open NodeConfig public
unquoteDecl ncOmbMe    ncConsensus = mkLens  (quote NodeConfig)
           (ncOmbMe ∷  ncConsensus ∷ [])

record RecoveryManager : Set where
  constructor RecoveryManager∙new
  field
    _rcmEpochState         : EpochState
    _rcmStorage            : PersistentLivenessStorage
    --_rcmStateComputer      : StateComputer
    _rcmLastCommittedRound : Round
open RecoveryManager public
unquoteDecl rcmEpochState   rcmStorage {-  rcmStateComputer-}  rcmLastCommittedRound = mkLens (quote RecoveryManager)
           (rcmEpochState ∷ rcmStorage {-∷ rcmStateComputer-} ∷ rcmLastCommittedRound ∷ [])

data RoundProcessor : Set where
  RoundProcessorRecovery : RecoveryManager → RoundProcessor
  RoundProcessorNormal   : RoundManager    → RoundProcessor

record EpochManager : Set where
  constructor mkEpochManager
  field
    _emAuthor             : Author
    _emConfig             : ConsensusConfig
    --_emStateComputer      : StateComputer
    _emStorage            : PersistentLivenessStorage
    _emSafetyRulesManager : SafetyRulesManager
    _emProcessor          : Maybe RoundProcessor
open EpochManager public
unquoteDecl emAuthor   emConfig {-  emStateComputer-}   emStorage   emSafetyRulesManager   emProcessor = mkLens (quote EpochManager)
           (emAuthor ∷ emConfig {-∷ emStateComputer-} ∷ emStorage ∷ emSafetyRulesManager ∷ emProcessor ∷ [])

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

record EpochRetrievalRequest : Set where
  constructor EpochRetrievalRequest∙new
  field
    _eprrqStartEpoch : Epoch
    _eprrqEndEpoch   : Epoch
unquoteDecl eprrqStartEpoch   eprrqEndEpoch   = mkLens (quote EpochRetrievalRequest)
           (eprrqStartEpoch ∷ eprrqEndEpoch ∷ [])
-- instance S.Serialize EpochRetrievalRequest

------------------------------------------------------------------------------
-- from LBFT.IO.OBM.Messages

record ECPWire : Set where
  constructor ECPWire∙new
  field
    --_ecpwWhy    : Text           -- for log visualization
    --_ecpwEpoch  : Epoch          -- for log visualization; epoch of sender
    --_ecpwRound  : Round          -- for log visualization; round of sender
    _ecpwECP      : EpochChangeProof
-- instance S.Serialize ECPWire

record EpRRqWire : Set where
  constructor EpRRqWire∙new
  field
    --_eprrqwWhy  : Text           -- for log visualization
    --_eprrqEpoch : Epoch          -- for log visualization; epoch of sender
    --_eprrqRound : Round          -- for log visualization; round of sender
    _eprrqEpRRq   : EpochRetrievalRequest
-- instance S.Serialize EpRRqWire

data Input : Set where
  IBlockRetrievalRequest    : Instant                  →          BlockRetrievalRequest  → Input
  IBlockRetrievalResponse   : Instant                  →          BlockRetrievalResponse → Input
  IEpochChangeProof         :           AccountAddress →          ECPWire                → Input
  IEpochRetrievalRequest    :           AccountAddress →          EpRRqWire              → Input
  IInit                     : Instant                                                    → Input
  IProposal                 : Instant → AccountAddress →          ProposalMsg            → Input
  IReconfigLocalEpochChange :                                   ReconfigEventEpochChange → Input
  ISyncInfo                 : Instant → AccountAddress →          SyncInfo               → Input
  ITimeout                  : Instant → String.String {-String is ThreadId-} → Epoch → Round → Input
  IVote                     : Instant → AccountAddress →          VoteMsg                → Input

