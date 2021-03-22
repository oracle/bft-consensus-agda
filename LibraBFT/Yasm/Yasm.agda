{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Yasm.Base as LYB

-- This module provides a single import for all Yasm modules

module LibraBFT.Yasm.Yasm
   (ℓ-EC        : Level)
   (EpochConfig : Set ℓ-EC)
   (epochId     : EpochConfig → EpochId)
   (authorsN    : EpochConfig → ℕ)
   (parms       : LYB.SystemParameters ℓ-EC EpochConfig epochId authorsN)
   (senderPKOK  : (ec : EpochConfig) → PK → LYB.SystemParameters.PeerId parms → Set)
  where
 open LYB.SystemParameters parms
 open import LibraBFT.Yasm.AvailableEpochs PeerId ℓ-EC EpochConfig epochId authorsN
             using (AvailableEpochs) renaming (lookup' to EC-lookup; lookup'' to EC-lookup') public
 open import LibraBFT.Yasm.Base       ℓ-EC EpochConfig epochId authorsN                      public
 open import LibraBFT.Yasm.System     ℓ-EC EpochConfig epochId authorsN parms                public
 open import LibraBFT.Yasm.Properties ℓ-EC EpochConfig epochId authorsN parms senderPKOK     public
