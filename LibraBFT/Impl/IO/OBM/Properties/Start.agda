{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties
import      LibraBFT.Impl.IO.OBM.GenKeyFile            as GenKeyFile
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Start
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open Invariants
open RoundManagerTransProps
open InitProofDefs

module LibraBFT.Impl.IO.OBM.Properties.Start where

module startViaConsensusProviderSpec
  (now : Instant)
  (nfl : GenKeyFile.NfLiwsVsVvPe)
  (txt : TxTypeDependentStuffForNetwork)
  where

  postulate
   contract' : EitherD-weakestPre (startViaConsensusProvider-ed-abs now nfl txt) InitContract
