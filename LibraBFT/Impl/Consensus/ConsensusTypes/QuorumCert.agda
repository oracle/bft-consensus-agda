{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert where

postulate
  verify : QuorumCert → ValidatorVerifier → ErrLog ⊎ Unit

