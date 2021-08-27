{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString                          as BS
import      LibraBFT.Base.Encode                              as S
open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.OBM.ConfigHardCoded                 as ConfigHardCoded
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Storage.DiemDB.DiemDB               as DiemDB
import      LibraBFT.Impl.Types.OnChainConfig.ValidatorSet    as ValidatorSet
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                       using (String)

module LibraBFT.Impl.Consensus.StateComputerByteString where

-- Note that this differs from the Haskell code, which still contains an errorExit.
-- TODO-2: better align these and re-review
compute : StateComputerComputeType
compute _self block _parentBlockId =
  StateComputeResult∙new
    (Version∙new (block ^∙ bEpoch {-∙ eEpoch-}) (block ^∙ bRound {-∙ rRound-}))
    <$> maybeEC
  -- In Rust, the following might throw BlockNotFound
  -- TODO execution_correctness_client.execute_block
 where
  getES : ByteString → Either (List String) EpochState

  maybeEC : Either (List String) (Maybe EpochState)
  maybeEC = case block ^∙ bBlockData ∙ bdBlockType of λ where
    (Proposal {-Payload [-}a{-])-} _author) →
      if BS∙isPrefixOf ConfigHardCoded.ePOCHCHANGE a then just <$> getES a else pure nothing
    NilBlock → pure nothing
    Genesis  → pure nothing

  getES bs = do
    let bs' = BS∙drop (BS∙length ConfigHardCoded.ePOCHCHANGE) bs
    case S.decode bs' of λ where
      (Left   e) → Left ("StateComputerByteString" ∷ "compute" ∷ "decode" ∷ {-T.pack-} e ∷ [])
      (Right vv) → Right (EpochState∙new (block ^∙ bEpoch + 1) vv)

-- LBFT-OBM-DIFF : gets block instead of vector of hashes
-- TODO-2: consider converting to EitherD before proving anything about this
commit : StateComputerCommitType
commit self db (ExecutedBlock∙new _b (StateComputeResult∙new version _)) liws =
  case (DiemDB.saveTransactions.E db (just liws)) of λ where
    (Left   e)  → Left (errText e)
    (Right db') → pure
       ( (self & scObmVersion ∙~ version)
       , db'
       , (maybeS (liws ^∙ liwsLedgerInfo ∙ liNextEpochState) nothing $ λ (EpochState∙new e vv) →
           just (ReconfigEventEpochChange∙new
                 (OnChainConfigPayload∙new e (ValidatorSet.obmFromVV vv))))
       )

-- LBFT-OBM-DIFF : completely different
syncTo : StateComputerSyncToType
syncTo liws =
  maybeS (liws ^∙ liwsNextEpochState) (Left ("StateComputerByteString" ∷ "syncTo" ∷ "Nothing" ∷ [])) $
         λ (EpochState∙new e vv) →
            Right  (ReconfigEventEpochChange∙new
                    (OnChainConfigPayload∙new e (ValidatorSet.obmFromVV vv)))

