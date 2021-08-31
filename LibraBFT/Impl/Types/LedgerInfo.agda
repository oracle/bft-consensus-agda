{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.BlockInfo             as BlockInfo
import      LibraBFT.Impl.Crypto.Crypto.Hash          as Hash
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto           as Crypto
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.LedgerInfo where

mockGenesis : Maybe ValidatorSet → LedgerInfo
mockGenesis mvs = LedgerInfo∙new (BlockInfo.mockGenesis mvs) Hash.valueZero
