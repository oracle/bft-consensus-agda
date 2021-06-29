{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.VoteData as VoteDataProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData            as VoteData
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures               as LedgerInfoWithSignatures
import      LibraBFT.Impl.Types.Properties.LedgerInfoWithSignatures    as LedgerInfoWithSignaturesProps
open import LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert          as QuorumCert
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

open RWST-do

module LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert (self : QuorumCert) (vv : ValidatorVerifier) where

  -- QuorumCert.verify is in Either monad, not LBFT

  -- Do we need to establish metatheory for dealing with the Either monad, similar to (but simpler
  -- than) weakest precondition?

  -- Here's the best I can do so far, but surely this is not the way forward!

  voteHash = hashVD (self ^∙ qcVoteData)

  record rnd≡0Props : Set where
    constructor mkRnd≡0Props
    field
        par≡cert : self ^∙ qcParentBlock ≡ self ^∙ qcCertifiedBlock
        cert≡li  : self ^∙ qcCertifiedBlock ≡ self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo
        noSigs   : Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) ≡ 0
  open rnd≡0Props

  record rnd≢0Props : Set where
    constructor mkRnd≢0Props
    field
      sigProp : LedgerInfoWithSignaturesProps.Contract (self ^∙ qcLedgerInfo) vv
      vdProp  : VoteDataProps.Contract (self ^∙ qcVoteData)
  open rnd≢0Props

  rnd≡0 = self ^∙ qcCertifiedBlock ∙ biRound ≡ 0

  record Contract : Set where
    constructor mkContract
    field
      lihash≡ : self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash ≡ voteHash
      rnd0    :   rnd≡0 → rnd≡0Props
      ¬rnd0   : ¬ rnd≡0 → rnd≢0Props
  open Contract

  contract : QuorumCert.verify self vv ≡ Right unit → Contract
  contract
     with (self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash) ≟Hash (hashVD (self ^∙ qcVoteData))
  ...| no neq = λ ()
  ...| yes refl
     with self ^∙ qcCertifiedBlock ∙ biRound ≟ 0
  ...| yes refl
     with (self ^∙ qcParentBlock) ≟-BlockInfo (self ^∙ qcCertifiedBlock)
  ...| no neq = λ ()
  ...| yes refl
     with (self ^∙ qcCertifiedBlock) ≟-BlockInfo (self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo)
  ...| no neq = λ ()
  ...| yes refl
     with Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) ≟ 0
  ...| yes noSigs = λ x → mkContract refl (λ _ → mkRnd≡0Props refl refl noSigs)
                                          (λ rnd≢0 → ⊥-elim (rnd≢0 refl))
  contract
     | yes refl
     | no neq
     with  LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)  vv | inspect
          (LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)) vv
  ...| Left  err  | _ = λ ()
  ...| Right unit | [ R ]
     with VoteData.verify (self ^∙ qcVoteData) | inspect
          VoteData.verify (self ^∙ qcVoteData)
  ...| Left err   | _ = λ ()
  ...| Right unit | [ R' ] = λ _ → mkContract refl (⊥-elim ∘ neq)
                                              λ x → mkRnd≢0Props (LedgerInfoWithSignaturesProps.contract (self ^∙ qcLedgerInfo) vv R)
                                                                 (VoteDataProps.contract (self ^∙ qcVoteData) R')
