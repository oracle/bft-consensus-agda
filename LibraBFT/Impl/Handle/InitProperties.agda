{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap                         as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Impl.Consensus.EpochManagerTypes
open import LibraBFT.Impl.Handle
import      LibraBFT.Impl.IO.OBM.GenKeyFile             as GenKeyFile
import      LibraBFT.Impl.OBM.Init                      as Init

module LibraBFT.Impl.Handle.InitProperties where

yyy : ∀ {x} → initEMWithOutput ≡ RightD x → initEMWithOutput' ≡ Right x
yyy iewo
  with GenKeyFile.create 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
... | Right (nf , _ , vss , vv , pe , liws)
  with Init.initialize 0 (nf , liws , vss , vv , pe) now ObmNeedFetch∙new pg
... | Right _
  with iewo
... | ()

yyy' : ∀ {x} → initEMWithOutput ≡ RightD x → initEMWithOutput' ≡ Right x
yyy' iewo
  with iewo
... | ()

module initEMWithOutputSpec where

  record ContractOk (em : EpochManager) (lo : List Output) : Set where
    constructor mkContractOk
    field
      a  : em ^∙ emAuthor ≡ 0
      c  : em ^∙ emConfig ≡
                          ConsensusConfig∙new (em ^∙ emAuthor) (em ^∙ emAuthor)
                           (SafetyRulesConfig∙new SRSLocal
                            (em ^∙ emConfig ∙ ccSafetyRules ∙ srcExportConsensusKey)
                            (Waypoint∙new (Version∙new (em ^∙ emAuthor) (em ^∙ emAuthor))
                             (em ^∙ emConfig ∙ ccSafetyRules ∙ srcObmGenesisWaypoint ∙ wValue)))
                           (em ^∙ emConfig ∙ ccSafetyRules ∙ srcExportConsensusKey)
      sc : em ^∙ emStateComputer ≡
                StateComputer∙new (Version∙new (em ^∙ emAuthor) (em ^∙ emAuthor))
      s  : em ^∙ emStorage ≡
                          MockStorage∙new
                            (mkMockSharedStorage (em ^∙ emStorage ∙ msSharedStorage ∙ mssBlock)
                             (em ^∙ emStorage ∙ msSharedStorage ∙ mssQc)
                             (em ^∙ emStorage ∙ msSharedStorage ∙ mssLis)
                             (em ^∙ emStorage ∙ msSharedStorage ∙ mssLastVote)
                             (em ^∙ emStorage ∙ msSharedStorage ∙ mssHighestTimeoutCertificate)
                             (ValidatorSet∙new ConsensusScheme∙new
                              (em ^∙ emStorage ∙ msSharedStorage ∙ mssValidatorSet ∙ vsPayload)))
                            (LedgerInfo∙new
                             (BlockInfo∙new (em ^∙ emAuthor) (em ^∙ emAuthor)
                              (em ^∙ emConfig ∙ ccSafetyRules ∙ srcObmGenesisWaypoint ∙ wValue)
                              (em ^∙ emConfig ∙ ccSafetyRules ∙ srcObmGenesisWaypoint ∙ wValue)
                              (Version∙new (em ^∙ emAuthor) (em ^∙ emAuthor))
                              (em ^∙ emStorage ∙ msStorageLedger ∙ liCommitInfo ∙ biNextEpochState))
                             (em ^∙ emConfig ∙ ccSafetyRules ∙ srcObmGenesisWaypoint ∙ wValue))
                            (DiemDB∙new
                             (mkLedgerStore
                              (em ^∙ emStorage ∙ msObmDiemDB ∙ ddbLedgerStore ∙ lsObmVersionToEpoch)
                              (em ^∙ emStorage ∙ msObmDiemDB ∙ ddbLedgerStore ∙ lsObmEpochToLIWS)
                              (em ^∙ emStorage ∙ msObmDiemDB ∙ ddbLedgerStore ∙ lsLatestLedgerInfo)))
      sr : em ^∙ emSafetyRulesManager ≡ mkSafetyRulesManager
                                         ((em ^∙ emSafetyRulesManager)
                                         SafetyRulesManager.srmInternalSafetyRules)
      p  : em ^∙ emProcessor ≡
        just
         (RoundProcessorNormal
          (RoundManager∙new
           ObmNeedFetch∙new
            (EpochState∙new (em ^∙ emAuthor)
                            (mkValidatorVerifier Map.empty 0 0))
            (BlockStore∙new (mkBlockTree {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})
                            (StateComputer∙new {!!})
                            (MockStorage∙new {!!} {!!} {!!}))
            (mkRoundState (mkExponentialTimeInterval 0 0.0 0)
                          0 0 0 (mkPendingVotes Map.empty nothing Map.empty) nothing)
            (ProposerElection∙new {!!})
            (ProposalGenerator∙new {!!})
            (mkSafetyRules {!!} {!!} {!!} {!!})
            false))

  Contract : Either ErrLog (EpochManager × List Output) → Set
  Contract (Left _) = ⊤
  Contract (Right (em , lo)) = ContractOk em lo

--  open initEMWithOutputSpec

  -- module _ (bt“ : BlockTree) (b : ExecutedBlock) (con : ContractOk bt“ b) where
  -- postulate
  --   contract' : EitherD-weakestPre (step₀ block bt) Contract

  -- contract : Contract (initEMWithOutput.E block bt)
  -- contract = EitherD-contract (step₀ block bt) Contract contract'

