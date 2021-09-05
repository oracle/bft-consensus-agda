{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All

module LibraBFT.Impl.Execution.ExecutorTypes.StateComputeResult where

extensionProof : StateComputeResult → AccumulatorExtensionProof
extensionProof self = AccumulatorExtensionProof∙new (self ^∙ scrObmNumLeaves)
