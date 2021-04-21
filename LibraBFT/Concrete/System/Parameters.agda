{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr
open        EpochConfig
open import LibraBFT.Yasm.Base (ℓ+1 0ℓ) EpochConfig epoch authorsN

-- In this module, we instantiate the system model with parameters to
-- model a system using the simple implementation model we have so
-- far, which aims to obey the VotesOnceRule, but not LockedRoundRule
-- yet.  This will evolve as we build out a model of a real
-- implementation.

module LibraBFT.Concrete.System.Parameters where
 ConcSysParms : SystemParameters
 ConcSysParms = mkSysParms
                 NodeId
                 _≟NodeId_
                 RoundManager
                 fakeRM
                 NetworkMsg
                 Vote
                 sig-Vote
                 _⊂Msg_
                 (_^∙ vEpoch)
                 initialRoundManagerAndMessages
                 peerStepWrapper
