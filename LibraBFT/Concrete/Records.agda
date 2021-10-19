{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        WithAbsVote

-- Here we have the abstraction functions that connect
-- the datatypes defined in LibraBFT.ImplFake.Consensus.Types
-- to the abstract records from LibraBFT.Abstract.Records
-- for a given EpochConfig.
--
module LibraBFT.Concrete.Records where

 ------------ properties relating the ids of (Executed)Blocks to hashes of their BlockData
 BlockHash≡ : Block → HashValue → Set
 BlockHash≡ b hv =  hashBlock b ≡ hv

 BlockId-correct : Block → Set
 BlockId-correct b = BlockHash≡ b (b ^∙ bId)

 BlockId-correct? : (b : Block) → Dec (BlockId-correct b)
 BlockId-correct? b = hashBlock b ≟Hash (b ^∙ bId)

 ExecutedBlockId-correct : ExecutedBlock → Set
 ExecutedBlockId-correct = BlockId-correct ∘ (_^∙ ebBlock)

 module WithEC (𝓔 : EpochConfig) where
   open import LibraBFT.ImplShared.Consensus.Types.EpochDep
   open WithEC 𝓔
   open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 ConcreteVoteEvidence as Abs hiding (bId; qcVotes; Block)
   open        EpochConfig 𝓔

   --------------------------------
   -- Abstracting Blocks and QCs --
   --------------------------------

   α-Block : Block → Abs.Block
   α-Block b with _bdBlockType (_bBlockData b)
   ...| NilBlock = record
        { bId     = _bId b
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

   α-Vote : (qc : QuorumCert)(valid : MetaIsValidQC qc) → ∀ {as} → as ∈ qcVotes qc → Abs.Vote
   α-Vote qc v {as} as∈QC = α-ValidVote (rebuildVote qc as)
                                        (_ivvMember (All-lookup (_ivqcMetaVotesValid v) as∈QC))

   -- Abstraction of votes produce votes that carry evidence
   -- they have been cast.
   α-Vote-evidence : (qc : QuorumCert)(valid : MetaIsValidQC qc)
                   → ∀{vs} (prf : vs ∈ qcVotes qc)
                   → ConcreteVoteEvidence (α-Vote qc valid prf)
   α-Vote-evidence qc valid {as} v∈qc
     = record { _cveVote        = rebuildVote qc as
              ; _cveIsValidVote = All-lookup (_ivqcMetaVotesValid valid) v∈qc
              ; _cveIsAbs       = refl
              }

   α-QC : Σ QuorumCert MetaIsValidQC → Abs.QC
   α-QC (qc , valid) = record
     { qCertBlockId = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
     ; qRound       = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
     ; qVotes       = All-reduce (α-Vote qc valid) All-self
     ; qVotes-C1    = subst IsQuorum {! !} (MetaIsValidQC._ivqcMetaIsQuorum valid)
     ; qVotes-C2    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
     ; qVotes-C3    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
     ; qVotes-C4    = All-reduce⁺ (α-Vote qc valid) (α-Vote-evidence qc valid) All-self
     }

   -- What does it mean for an (abstract) Block or QC to be represented in a NetworkMsg?
   data _α-∈NM_ : Abs.Record → NetworkMsg → Set where
     qc∈NM : ∀ {cqc nm}
           → (valid : MetaIsValidQC cqc)
           → cqc QC∈NM nm
           → Abs.Q (α-QC (cqc , valid)) α-∈NM nm
     b∈NM  : ∀ {cb pm nm}
           → nm ≡ P pm
           → pm ^∙ pmProposal ≡ cb
           → Abs.B (α-Block cb) α-∈NM nm

   -- Our system model contains a message pool, which is a list of NodeId-NetworkMsg pairs.  The
   -- following relation expresses that an abstract record r is represented in a given message pool
   -- sm.
   data _α-Sent_ (r : Abs.Record) (sm : List (NodeId × NetworkMsg)) : Set where
     ws : ∀ {p nm} → getEpoch nm ≡ epoch → (p , nm) ∈ sm → r α-∈NM nm → r α-Sent sm

