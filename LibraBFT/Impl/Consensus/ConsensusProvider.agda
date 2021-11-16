{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.EpochManager           as EpochManager
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage  as MockStorage
import      LibraBFT.Impl.Types.OnChainConfig.ValidatorSet as ValidatorSet
import      LibraBFT.Impl.Types.ValidatorSigner            as ValidatorSigner
import      LibraBFT.Impl.Types.Waypoint                   as Waypoint
import      LibraBFT.Impl.IO.OBM.GenKeyFile                as GenKeyFile
import      LibraBFT.Impl.OBM.ConfigHardCoded              as ConfigHardCoded
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude                               hiding (_++_)
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                    using (String; _++_)

module LibraBFT.Impl.Consensus.ConsensusProvider where

obmInitialData
  : GenKeyFile.NfLiwsVsVvPe
  → Either ErrLog
           (NodeConfig × OnChainConfigPayload × LedgerInfoWithSignatures × SK × ProposerElection)
obmInitialData ( _numFaults , genesisLIWS , validatorSigner
               , validatorVerifier , proposerElection ) = do
  let vs   = ValidatorSet.obmFromVV validatorVerifier
      occp = onChainConfigPayload vs
  wp       ← Waypoint.newEpochBoundary (genesisLIWS ^∙ liwsLedgerInfo)
  let nc   = nodeConfig wp
  pure (nc , occp , genesisLIWS , validatorSigner ^∙ vsPrivateKey , proposerElection)
 where
  onChainConfigPayload : ValidatorSet → OnChainConfigPayload
  onChainConfigPayload = OnChainConfigPayload∙new ({-Epoch-} 1)

  nodeConfig : Waypoint → NodeConfig
  nodeConfig genesisWaypoint =
    record -- NodeConfig
    { _ncObmMe     = validatorSigner ^∙ vsAuthor
    ; _ncConsensus = record -- ConsensusConfig
      { _ccMaxPrunedBlocksInMem  = ConfigHardCoded.maxPrunedBlocksInMem
      ; _ccRoundInitialTimeoutMS = ConfigHardCoded.roundInitialTimeoutMS
      ; _ccSafetyRules           = record -- SafetyRulesConfig
        { _srcService                     = SRSLocal
        ; _srcExportConsensusKey          = true
        ; _srcObmGenesisWaypoint          = genesisWaypoint
        }
      ; _ccSyncOnly              = false
      }
    }

abstract
  obmInitialData-ed-abs
    : GenKeyFile.NfLiwsVsVvPe
    → EitherD ErrLog
              (NodeConfig × OnChainConfigPayload × LedgerInfoWithSignatures × SK × ProposerElection)
  obmInitialData-ed-abs = fromEither ∘ obmInitialData

------------------------------------------------------------------------------

-- LBFT-OBM-DIFF
-- 'start_consensus' in Rust inits and loops
-- that is split so 'startConsensus' returns init data
-- then loop is called with that data.
module startConsensus-ed
  (nodeConfig : NodeConfig)
  -- BEGIN OBM
  (obmNow               : Instant)
  (obmPayload           : OnChainConfigPayload)
  (obmGenesisLIWS       : LedgerInfoWithSignatures)
  (obmSK                : SK)
  (obmNeedFetch         : ObmNeedFetch)
  (obmProposalGenerator : ProposalGenerator)
  (obmStateComputer     : StateComputer)
  where
  -- END OBM

  step₁ : ValidatorSet → (RecoveryData × PersistentLivenessStorage) → EitherD ErrLog (EpochManager × List Output)
  step₂ : PersistentLivenessStorage → ValidatorInfo → EitherD ErrLog (EpochManager × List Output)

  step₀ : EitherD ErrLog (EpochManager × List Output)
  step₀ = do
    let obmValidatorSet = obmPayload ^∙ occpObmValidatorSet
    eitherS (MockStorage.startForTesting obmValidatorSet (just obmGenesisLIWS)) LeftD (step₁ obmValidatorSet)

  step₁ obmValidatorSet (_obmRecoveryData , persistentLivenessStorage) = do
        let stateComputer = obmStateComputer
        eitherS (ValidatorSet.obmGetValidatorInfo (nodeConfig ^∙ ncObmMe) obmValidatorSet) LeftD (step₂ persistentLivenessStorage)

  step₂ persistentLivenessStorage vi = do
          eitherS (EpochManager.new nodeConfig stateComputer persistentLivenessStorage
                            (vi ^∙ viAccountAddress) obmSK) LeftD $
                   λ epochMgr →
                       EpochManager.start
                         epochMgr obmNow
                         obmPayload obmNeedFetch obmProposalGenerator
                         obmGenesisLIWS

abstract
  startConsensus-ed-abs = startConsensus-ed.step₀
  startConsensus-ed-abs-≡ : startConsensus-ed-abs ≡ startConsensus-ed.step₀
  startConsensus-ed-abs-≡ = refl

