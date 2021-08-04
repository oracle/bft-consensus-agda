{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo as SI
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

  record SIVerifyProps (pre : RoundManager) (rmc : RoundManager-correct pre) : Set where
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
       syncResCorr   : r ≡ Right unit → ∀ rmc → SIVerifyProps pre rmc
       -- Signatures
       -- TODO-2: What requirements on `self` are needed to show `QCProps.OutputQc∈RoundManager outs pre`

   verifyCorrect : SI.verify self validator ≡ Right unit → (rmc : RoundManager-correct pre) → SIVerifyProps pre rmc
   verifyCorrect verify≡ rmc
      with epoch ≟ self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biEpoch
   ...| no  ep≢ = absurd (Left _ ≡ Right _) case verify≡ of λ ()
   ...| yes sivpEp≡
      with sivpTcEp≡ verify≡
      where
      sivpTcEp≡ : SI.verify.step₁ self validator ≡ Right unit
                  → maybeS (self ^∙ siHighestTimeoutCert) Unit (\tc -> epoch ≡ tc ^∙ tcEpoch)
                    × SI.verify.step₂ self validator ≡ Right unit
      sivpTcEp≡ verify≡₁
         with self ^∙ siHighestTimeoutCert
      ...| nothing = unit , verify≡₁
      ...| just tc
         with epoch ≟ tc ^∙ tcEpoch
      ...| yes tce≡ = tce≡ , verify≡₁
      ...| no  tce≢ = absurd (Left _ ≡ Right _) case verify≡₁ of λ ()
   ...| sivpTcEp≡ , verify≡₂
      with sivpHqc≥Hcc verify≡₂
      where
      sivpHqc≥Hcc : (SI.verify.step₂ self validator ≡ Right unit)
                    → (self ^∙ siHighestQuorumCert) [ _≥_ ]L self ^∙ siHighestCommitCert at qcCertifiedBlock ∙ biRound
                      × SI.verify.step₃ self validator ≡ Right unit
      sivpHqc≥Hcc verify≡₂
         with    self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biRound
              ≥? self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biRound
      ...| yes hqc≥hcc = hqc≥hcc , verify≡₂
      ...| no  hqc<hcc = absurd Left _ ≡ Right _ case verify≡₂ of λ ()
   ...| sivpHqc≥Hcc , verify≡₃
      with sivpHqc≢empty verify≡₃
      where
      sivpHqc≢empty : (SI.verify.step₃ self validator ≡ Right unit)
                      → self ^∙ siHighestCommitCert ∙ qcCommitInfo ≢ BI.empty
                        × SI.verify.step₄ self validator ≡ Right unit
      sivpHqc≢empty verify≡₃
         with self ^∙ siHighestCommitCert ∙ qcCommitInfo ≟ BI.empty
      ...| no  ≢empty = ≢empty , verify≡₃
      ...| yes ≡empty = absurd Left _ ≡ Right _ case verify≡₃ of λ ()
   ...| sivpHqc≢empty , verify≡₄ =
   -- TODO: continue case analysis for remaining fields
     record
     { sivpEp≡       = sivpEp≡
     ; sivpTcEp≡     = sivpTcEp≡
     ; sivpHqc≥Hcc   = sivpHqc≥Hcc
     ; sivpHqc≢empty = sivpHqc≢empty
     ; sivpHqcVer    = obm-dangerous-magic' "TODO"
     ; sivpHccVer    = obm-dangerous-magic' "TODO"
     ; sivpHtcVer    = obm-dangerous-magic' "TODO"
     }

   contract : LBFT-weakestPre (SI.verifyM self validator) Contract pre
   contract = mkContract id refl refl verifyCorrect
