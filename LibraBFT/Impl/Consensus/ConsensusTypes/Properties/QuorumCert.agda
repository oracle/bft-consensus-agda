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
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert (self : QuorumCert) (vv : ValidatorVerifier) where
  voteHash = hashVD (self ^∙ qcVoteData)

  record rnd≡0Props : Set where
    field
        par≡cert : self ^∙ qcParentBlock    ≡ self ^∙ qcCertifiedBlock
        cert≡li  : self ^∙ qcCertifiedBlock ≡ self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo
        noSigs   : Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) ≡ 0
  open rnd≡0Props

  record rnd≢0Props : Set where
    field
      sigProp : LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo) vv ≡ Right unit
      vdProp  : VoteDataProps.Contract (self ^∙ qcVoteData)
  open rnd≢0Props

  ParentProps : Dec (self ^∙ qcCertifiedBlock ∙ biRound ≡ 0) → Set
  ParentProps (yes _) = rnd≡0Props
  ParentProps (no  _) = rnd≢0Props

  record Contract : Set where
    field
      lihash≡ : self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash ≡ voteHash
      rnd≟0   : Dec (self ^∙ qcCertifiedBlock ∙ biRound ≡ 0)
      parProp : ParentProps rnd≟0
  open Contract

  contract : ∀ (r : Either ErrLog Unit) → r ≡ Right unit
           → QuorumCert.verify self vv ≡ r
           → Contract
  contract (Left fakeErr)
     with (self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash) ≟Hash
          (hashVD (self ^∙ qcVoteData))
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
  ...| yes noSigs = λ ()

  contract (Right unit)
     with (self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash) ≟Hash (hashVD (self ^∙ qcVoteData))
  ...| no neq = λ _ ()
  ...| yes refl
     with self ^∙ qcCertifiedBlock ∙ biRound ≟ 0
  ...| yes refl
     with (self ^∙ qcParentBlock) ≟-BlockInfo (self ^∙ qcCertifiedBlock)
  ...| no neq = λ _ ()
  ...| yes refl
     with (self ^∙ qcCertifiedBlock) ≟-BlockInfo (self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo)
  ...| no neq = λ _ ()
  ...| yes refl
     with Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) ≟ 0
  ...| yes noSigs = λ _ _ →
         record { lihash≡ = refl
                ; rnd≟0 = yes refl
                ; parProp = record { par≡cert = refl
                                   ; cert≡li = refl
                                   ; noSigs = noSigs } }
  contract (Right unit)
     | yes refl
     | no neq
     with  LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)  vv | inspect
          (LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)) vv
  ...| Left  err  | [ R ] = λ _ ()
  ...| Right unit | [ R ]
     with VoteData.verify (self ^∙ qcVoteData) | inspect
          VoteData.verify (self ^∙ qcVoteData)
  ...| Left err   | _ = λ _ ()
  ...| Right unit | [ R' ] = λ _ _ →
         record { lihash≡ = refl
                ; rnd≟0 = no neq
                ; parProp = record { sigProp = R
                                   ; vdProp = VoteDataProps.contract (self ^∙ qcVoteData) R' } }
