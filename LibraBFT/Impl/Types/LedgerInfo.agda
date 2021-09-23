{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Types.BlockInfo             as BlockInfo
import      LibraBFT.Impl.Crypto.Crypto.Hash          as Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.Types.LedgerInfo where

mockGenesis : Maybe ValidatorSet → Either ErrLog LedgerInfo
mockGenesis mvs = LedgerInfo∙new <$> BlockInfo.mockGenesis mvs <*> pure Hash.valueZero
