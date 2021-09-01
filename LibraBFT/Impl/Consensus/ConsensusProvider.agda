{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.EpochManager           as EpochManager
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage  as MockStorage
open import LibraBFT.Impl.Types.OnChainConfig.ValidatorSet as ValidatorSet
open import LibraBFT.Impl.Types.ValidatorSigner            as ValidatorSigner
open import LibraBFT.Impl.Types.Waypoint                   as Waypoint
open import LibraBFT.Impl.OBM.ConfigHardCoded              as ConfigHardCoded
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.Prelude                               hiding (_++_)
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                    using (String; _++_)

module LibraBFT.Impl.Consensus.ConsensusProvider where

NfLiwsVssVvPe =
  (U64 × LedgerInfoWithSignatures × List ValidatorSigner × ValidatorVerifier × ProposerElection)

-- IMPL-DIFF: Haskell uses panic/errorExit.  This version uses Either.
obmInitialData
  : AuthorName
  → {-GenKeyFile.-}NfLiwsVssVvPe
  → Either String (NodeConfig × OnChainConfigPayload × LedgerInfoWithSignatures × SK × ProposerElection)
obmInitialData me ( _numFaults , genesisLIWS , validatorSigners
                  , validatorVerifier , proposerElection ) = do
  let vs   = ValidatorSet.obmFromVV validatorVerifier
      occp = onChainConfigPayload vs
  wp       ← eitherS (Waypoint.newEpochBoundary (genesisLIWS ^∙ liwsLedgerInfo))
                     (\e → Left (here' ++ errText' e))
                     Right
  let nc   = nodeConfig wp
  eitherS (ValidatorSigner.obmGetValidatorSigner (nc ^∙ ncObmMe) validatorSigners)
          (λ e → Left (here' ++ errText' e))
          (λ vsigner →
            Right (nc , occp , genesisLIWS , vsigner ^∙ vsPrivateKey , proposerElection))
 where
  here' : String
  here' = "ConsensusProvider.obmInitialData' "

  onChainConfigPayload : ValidatorSet → OnChainConfigPayload
  onChainConfigPayload = OnChainConfigPayload∙new ({-Epoch-} 1)

  nodeConfig : Waypoint → NodeConfig
  nodeConfig genesisWaypoint =
    record -- NodeConfig
    { _ncObmMe     = me
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

------------------------------------------------------------------------------

-- LBFT-OBM-DIFF
-- 'start_consensus' in Rust inits and loops
-- that is split so 'startConsensus' returns init data
-- then loop is called with that data.
-- IMPL-DIFF: This is IO (Either ...) in Haskell.   Just Either here.
startConsensus
  : Instant -- IMPL-DIFF
  → NodeConfig
  -- BEGIN OBM
  → OnChainConfigPayload → LedgerInfoWithSignatures → SK
  → ObmNeedFetch → ProposalGenerator → StateComputer
  -- END OBM
  → Either ErrLog (EpochManager × List Output)
startConsensus obmNow
               nodeConfig
               obmPayload obmGenesisLIWS obmSK
               obmNeedFetch obmProposalGenerator obmStateComputer = do
  let obmValidatorSet = obmPayload ^∙ occpObmValidatorSet
  case MockStorage.startForTesting obmValidatorSet (just obmGenesisLIWS) of λ where
    (Left e) → Left e
    (Right (_obmRecoveryData , persistentLivenessStorage)) → do
      let stateComputer = obmStateComputer
      case ValidatorSet.obmGetValidatorInfo (nodeConfig ^∙ ncObmMe) obmValidatorSet of λ where
        (Left   e) → Left e
        (Right vi) → case EpochManager.new nodeConfig {-stateComputer-} persistentLivenessStorage
                          (vi ^∙ viAccountAddress) obmSK of λ where
          (Left  e)        → Left e
          (Right epochMgr) → do
            -- obmNow <- Time.getCurrentInstant
            EpochManager.start
              epochMgr obmNow
              obmPayload obmNeedFetch obmProposalGenerator
              obmGenesisLIWS
