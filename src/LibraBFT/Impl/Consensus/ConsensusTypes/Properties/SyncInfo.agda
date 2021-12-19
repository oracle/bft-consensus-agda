{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert as QC
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert            as QuorumCert
open import LibraBFT.Impl.Consensus.ConsensusTypes.SyncInfo as SI
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Impl.Types.BlockInfo as BI
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open Invariants
open RoundManagerTransProps

module LibraBFT.Impl.Consensus.ConsensusTypes.Properties.SyncInfo where

module verifyMSpec (self : SyncInfo) (validator : ValidatorVerifier) where

  epoch = self ^∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biEpoch

  record SIVerifyProps (pre : RoundManager) : Set where
    field
      sivpEp≡       : epoch ≡ self ^∙ siHighestCommitCert ∙ qcCertifiedBlock ∙ biEpoch
      sivpTcEp≡     : maybeS (self ^∙ siHighestTimeoutCert) Unit $ λ tc -> epoch ≡ tc ^∙ tcEpoch
      sivpHqc≥Hcc   : (self ^∙ siHighestQuorumCert) [ _≥_ ]L self ^∙ siHighestCommitCert at qcCertifiedBlock ∙ biRound
      sivpHqc≢empty : self ^∙ siHighestCommitCert ∙ qcCommitInfo ≢ BI.empty
      sivpHqcVer    : QC.Contract (self ^∙ siHighestQuorumCert) validator
      sivpHccVer    : maybeS (self ^∙ sixxxHighestCommitCert) Unit $ λ qc → QC.Contract qc validator
      -- Waiting on TimeoutCertificate Contract : sivpHtcVer    : maybeS (self ^∙ siHighestTimeoutCert  ) Unit $ λ tc → {!!}

  module _ (pre : RoundManager) where

   record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
     constructor mkContract
     field
       -- General properties / invariants
       rmInv         : Preserves RoundManagerInv pre post
       noStateChange : pre ≡ post
       -- Output
       noMsgOuts     : OutputProps.NoMsgs outs
       -- Syncing
       syncResCorr   : r ≡ Right unit → SIVerifyProps pre
       -- NOTE: Since the output contains no messages and the state does not
       -- change, nothing needs to be said about the quorum certificats in the
       -- output and post state

   verifyCorrect : SI.verify self validator ≡ Right unit → SIVerifyProps pre
   verifyCorrect verify≡
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
   ...| sivpHqc≢empty , verify≡₄
      with sivpHqcVer verify≡₄
      where
      sivpHqcVer : (SI.verify.step₄ self validator ≡ Right unit)
                   → QC.Contract (self ^∙ siHighestQuorumCert) validator
                     × SI.verify.step₅ self validator ≡ Right unit
      sivpHqcVer verify≡₄
         with  QuorumCert.verify (self ^∙ siHighestQuorumCert)  validator | inspect
              (QuorumCert.verify (self ^∙ siHighestQuorumCert)) validator
      ...| Left  _    | _ = absurd Left _ ≡ Right _ case verify≡₄ of λ ()
      ...| Right unit | [ R ]
         with QC.contract (self ^∙ siHighestQuorumCert) validator (Right unit) refl R
      ...| qcCon = qcCon , verify≡₄
   ...| sivpHqcVer , verify≡₅
      with sivpHccVer verify≡₅
      where
      sivpHccVer : (SI.verify.step₅ self validator ≡ Right unit)
                   → (maybeS (self ^∙ sixxxHighestCommitCert) Unit $ λ qc → QC.Contract qc validator)
                     × SI.verify.step₆ self validator ≡ Right unit
      sivpHccVer verify≡₅
         with self ^∙ sixxxHighestCommitCert
      ...| nothing = unit , verify≡₅
      ...| just qc
         with QuorumCert.verify  qc  validator | inspect
              (QuorumCert.verify qc) validator
      ...| Left _ | _ = absurd Left _ ≡ Right _ case verify≡₅ of λ ()
      ...| Right unit | [ R ] = QC.contract qc validator (Right unit) refl R , verify≡₅
   ...| sivpHccVer , verify≡₆ =
   -- TODO: continue case analysis for remaining fields
     record
     { sivpEp≡       = sivpEp≡
     ; sivpTcEp≡     = sivpTcEp≡
     ; sivpHqc≥Hcc   = sivpHqc≥Hcc
     ; sivpHqc≢empty = sivpHqc≢empty
     ; sivpHqcVer    = sivpHqcVer
     ; sivpHccVer    = sivpHccVer
     -- ; sivpHtcVer =
     }

   contract : ∀ Q → (RWS-Post-⇒ Contract Q) → LBFT-weakestPre (SI.verifyM self validator) Q pre
   contract Q pf = LBFT-⇒ (SI.verifyM self validator) pre (mkContract id refl refl verifyCorrect) pf
