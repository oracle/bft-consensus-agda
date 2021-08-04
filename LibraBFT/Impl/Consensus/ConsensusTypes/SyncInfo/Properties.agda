{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Impl.Types.BlockInfo as BI
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo.Properties where

module verifyMSpec (self : SyncInfo) (validator : ValidatorVerifier) where

  epoch = self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biEpoch

  record SIVerifyProps (pre post : RoundManager) (rmc : RoundManager-correct pre) : Set where
    field
      sivpEp≡       : epoch ≡ self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biEpoch
      sivpTcEp≡     : maybeS (self ^∙ siHighestTimeoutCert) Unit (\tc -> epoch ≡ tc ^∙ tcEpoch)
      sivpHqc≥Hcc   : (self ^∙ siHighestQuorumCert) [ _≥_ ]L self ^∙ siHighestCommitCert at qcCertifiedBlock ∙ biRound
      sivpHqc≢empty : self ^∙ siHighestCommitCert ∙ qcCommitInfo ≢ BI.empty
      sivpHqcVer    : WithEC.MetaIsValidQC (α-EC (pre , rmc)) (self ^∙ siHighestQuorumCert)
      sivpHccVer    : maybeS (self ^∙ sixxxHighestCommitCert) Unit (WithEC.MetaIsValidQC          (α-EC (pre , rmc)))
      sivpHtcVer    : maybeS (self ^∙ siHighestTimeoutCert  ) Unit (WithEC.MetaIsValidTimeoutCert (α-EC (pre , rmc)))

  module _ (pool : SentMessages) (pre : RoundManager) where

   record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
     constructor mkContract
     field
       -- General properties / invariants
       rmInv         : Preserves (RoundManagerInv pool) pre post
       noStateChange : pre ≡ post
       -- Output
       noMsgOuts     : OutputProps.NoMsgs outs
       -- Syncing
       syncResCorr   : r ≡ Right unit → ∀ rmc → SIVerifyProps pre post rmc
       -- Signatures
       -- TODO-2: What requirements on `self` are needed to show `QCProps.OutputQc∈RoundManager outs pre`
