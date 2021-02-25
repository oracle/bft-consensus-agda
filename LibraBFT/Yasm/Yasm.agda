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
   (NodeId      : Set)
   (ℓ-EC        : Level)
   (EpochConfig : Set ℓ-EC)
   (epochId     : EpochConfig → EpochId)
   (authorsN    : EpochConfig → ℕ)
   (getPubKey   : (ec : EpochConfig) → LYB.Member NodeId ℓ-EC EpochConfig epochId authorsN ec → PK)
   (parms       : LYB.SystemParameters NodeId ℓ-EC EpochConfig epochId authorsN)
  where
 open import LibraBFT.Yasm.AvailableEpochs NodeId ℓ-EC EpochConfig epochId authorsN
             using (AvailableEpochs) renaming (lookup' to EC-lookup; lookup'' to EC-lookup')                          public
 open import LibraBFT.Yasm.Base       NodeId ℓ-EC EpochConfig epochId authorsN                 public
 open import LibraBFT.Yasm.System     NodeId ℓ-EC EpochConfig epochId authorsN           parms public
 open import LibraBFT.Yasm.Properties NodeId ℓ-EC EpochConfig epochId authorsN getPubKey parms public
