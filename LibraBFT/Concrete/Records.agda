{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types.EpochIndep
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        WithAbsVote

-- Here we have the abstraction functions that connect
-- the datatypes defined in LibraBFT.Impl.Consensus.Types
-- to the abstract records from LibraBFT.Abstract.Records
-- for a given EpochConfig.
--
module LibraBFT.Concrete.Records (𝓔 : EpochConfig) where
 open import LibraBFT.Impl.Consensus.Types.EpochDep 𝓔
 open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 ConcreteVoteEvidence as Abs hiding (bId; qcVotes; Block)
 open        EpochConfig 𝓔
 --------------------------------
 -- Abstracting Blocks and QCs --
 --------------------------------

 α-Block : Block → Abs.Block
 α-Block b with ₋bdBlockType (₋bBlockData b)
 ...| NilBlock = record
      { bId     = ₋bId b
      ; bPrevQC = just (b ^∙ (bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙  vdParent ∙ biId))
      ; bRound  = b ^∙ bBlockData ∙ bdRound
      }
 ...| Genesis = record
      { bId     = b ^∙ bId
      ; bPrevQC = nothing
      ; bRound  = b ^∙ bBlockData ∙ bdRound
      }
 ...| Proposal cmd α = record
      { bId     = b ^∙ bId
      ; bPrevQC = just (b ^∙ bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙ vdParent ∙ biId)
      ; bRound  = b ^∙ bBlockData ∙ bdRound
      }

 α-VoteData-Block : VoteData → Abs.Block
 α-VoteData-Block vd = record
      { bId     = vd ^∙ vdProposed ∙ biId
      ; bPrevQC = just (vd ^∙ vdParent ∙ biId)
      ; bRound  = vd ^∙ vdProposed ∙ biRound
      }

 α-Vote : (qc : QuorumCert)(valid : IsValidQC qc) → ∀ {as} → as ∈ qcVotes qc → Abs.Vote
 α-Vote qc v {as} as∈QC = α-ValidVote (rebuildVote qc as)
                                      (₋ivvMember (All-lookup (₋ivqcVotesValid v) as∈QC))

 -- Abstraction of votes produce votes that carry evidence
 -- they have been cast.
 α-Vote-evidence : (qc : QuorumCert)(valid : IsValidQC qc)
                 → ∀{vs} (prf : vs ∈ qcVotes qc)
                 → ConcreteVoteEvidence (α-Vote qc valid prf)
 α-Vote-evidence qc valid {as} v∈qc
   = record { ₋cveVote        = rebuildVote qc as
            ; ₋cveIsValidVote = All-lookup (₋ivqcVotesValid valid) v∈qc
            ; ₋cveIsAbs       = refl
            }

 voteInEvidence≈rebuiltVote
        : ∀ {vd cqc valid as}
        → (as∈cqc : Any (_≡_ as) (qcVotes cqc))
        → (ev : ConcreteVoteEvidence vd)
        → vd ≡ α-Vote cqc valid as∈cqc
        → ₋cveVote ev ≈Vote rebuildVote cqc as
 voteInEvidence≈rebuiltVote {_} {cqc} {valid} {α , sig , ord} as∈cqc ev refl
   = equivVotes (cong abs-vBlockUID (₋cveIsAbs ev))
                (cong abs-vRound (₋cveIsAbs ev))
                (member≡⇒author≡
                  (isJust (₋ivvAuthor (₋cveIsValidVote ev)))
                  (isJust (₋ivvAuthor (All-lookup (₋ivqcVotesValid valid) as∈cqc)))
                  (trans (to-witness-isJust-≡ {prf = ₋ivvAuthor (₋cveIsValidVote ev)})
                         (trans (cong abs-vMember (₋cveIsAbs ev))
                                (sym (to-witness-isJust-≡ {prf = ₋ivvAuthor (All-lookup (₋ivqcVotesValid valid) as∈cqc)}))))
                )

 α-QC : Σ QuorumCert IsValidQC → Abs.QC
 α-QC (qc , valid) = record
   { qCertBlockId = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
   ; qRound       = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
   ; qVotes       = All-reduce (α-Vote qc valid) All-self
   ; qVotes-C1    = {! IsValidQC.₋ivqcIsQuorum valid!}
   ; qVotes-C2    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
   ; qVotes-C3    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
   ; qVotes-C4    = All-reduce⁺ (α-Vote qc valid) (α-Vote-evidence qc valid) All-self
   }

 -- What does it mean for an (abstract) Block or QC to be represented in a NetworkMsg?
 data _α-∈NM_ : Abs.Record → NetworkMsg → Set where
   qc∈NM : ∀ {cqc q nm}
         → (valid : IsValidQC cqc)
         → cqc QC∈NM nm
         → q ≡ α-QC (cqc , valid)
         → (Abs.Q q) α-∈NM nm
   b∈NM  : ∀ {cb pm nm}
         → nm ≡ P pm
         → pm ^∙ pmProposal ≡ cb
         → (Abs.B (α-Block cb)) α-∈NM nm

 -- Our abstract system contains a message pool, which is a list of NodeId-NetworkMsg pairs.  The
 -- following relation expresses that an abstract record r is represented in a given message pool
 -- sm.
 data _α-Sent_ (r : Abs.Record) (sm : List (NodeId × NetworkMsg)) : Set where
   i  : r ≡ Abs.I → r α-Sent sm
   ws : ∀ {p nm} → getEpoch nm ≡ epochId → (p , nm) ∈ sm → r α-∈NM nm → r α-Sent sm
