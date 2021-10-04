{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap                            as Map
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

-- This module defines types for connecting abstract and concrete
-- votes by defining what constitutes enough "evidence" that a
-- vote was cast, which is passed around in the abstract model as
-- the variable (𝓥 : VoteEvidence); here we instantiate it to
-- 'ConcreteVoteEvidence'.
--
-- Some of the types in this module depend on an EpochConfig, but
-- never inspect it. Consequently, we define everything over an
-- abstract 𝓔 passed around as module parameter to an inner module
-- WithEC.  Before that, we define some definitions relevant to
-- constructing EpochConfigs from RoundManager.

module LibraBFT.ImplShared.Consensus.Types.EpochDep where

-- Note that the definitions below are relevant only to the verification, not the implementation.
-- They should probably move somewhere else.

-- ValidatorVerifier-correct imposes requirements on a ValidatorVerifier that are sufficient to
-- ensure that we can construct an abstract EpochConfig based on it (see α-EC-VV below).
ValidatorVerifier-correct : ValidatorVerifier → Set
ValidatorVerifier-correct vv =
  let authorsInfo    = List-map proj₂ (kvm-toList (vv ^∙ vvAddressToValidatorInfo))
      totalVotPower  = f-sum (_^∙ vciVotingPower) authorsInfo
      quorumVotPower = vv ^∙ vvQuorumVotingPower
      bizF           = totalVotPower ∸ quorumVotPower
      pksAll≢        = ∀ v₁ v₂ nId₁ nId₂ → nId₁ ≢ nId₂
                       → lookup nId₁ (vv ^∙ vvAddressToValidatorInfo) ≡ just v₁
                       → lookup nId₂ (vv ^∙ vvAddressToValidatorInfo) ≡ just v₂
                       → v₁ ^∙ vciPublicKey ≢ v₂ ^∙ vciPublicKey
   in   3 * bizF       < totalVotPower
      × quorumVotPower ≤ totalVotPower
      × pksAll≢
      × f-sum (_^∙ vciVotingPower) (List-filter (Meta-DishonestPK? ∘ (_^∙ vciPublicKey)) authorsInfo) ≤ bizF

open DecLemmas {A = NodeId} _≟_
import LibraBFT.Abstract.BFT

-- α-EC-VV computes an abstract EpochConfig given a ValidatorVerifier
-- that satisfies the conditions stipulated by ValidVerifier-correct
α-EC-VV : Σ ValidatorVerifier ValidatorVerifier-correct → Epoch → EpochConfig
α-EC-VV (vv , ok) epoch =
      EpochConfig∙new bsId
                      epoch
                      numAuthors
                      toNodeId
                      (list-index (_≟_ ∘ proj₁) authors)
                      (index∘lookup-id authors proj₁ authorsIDs≢)
                      (λ lkp≡α → lookup∘index-id authors proj₁ authorsIDs≢ lkp≡α)
                      getPubKey
                      getPKey-Inj
                      (λ quorum → qsize ≤ VotPowerMembers quorum
                                   × allDistinct quorum)
                      λ q₁ q₂ → LibraBFT.Abstract.BFT.bft-lemma
                                  numAuthors
                                  (_^∙ vciVotingPower ∘ getAuthorInfo)
                                  (f-sum (_^∙ vciVotingPower) authorsInfo ∸ qsize)
                                  (≤-trans (proj₁ ok) (≡⇒≤ totalVotPower≡))
                                  getPubKey
                                  (let disMembers  = List-filter (Meta-DishonestPK? ∘ getPubKey) members
                                       sumDisM≡    = sum-f∘g disMembers (_^∙ vciVotingPower) getAuthorInfo
                                       disM≡disNId = map∘filter members authorsInfo getAuthorInfo
                                                                (Meta-DishonestPK? ∘ (_^∙ vciPublicKey)) getAuthInfo≡VCI
                                       sumDis≤bizF = (proj₂ ∘ proj₂ ∘ proj₂) ok
                                   in ≤-trans (≡⇒≤ (trans sumDisM≡ (cong (f-sum _vciVotingPower) disM≡disNId))) sumDis≤bizF)
                                  (proj₂ q₁) (proj₂ q₂)
                                  (≤-trans (≡⇒≤ N∸bizF≡Qsize) (proj₁ q₁))
                                  (≤-trans (≡⇒≤ N∸bizF≡Qsize) (proj₁ q₂))
                              -- TODO-2: this takes the per-epoch genesisUID from the GenesisInfo
                              -- for the *first* epoch (soon to be renamed to BootStrapInfo avoid
                              -- this confusion).  This is temporary until we do epoch change; then
                              -- it will need to be provided by the caller.
      where bsId            = fakeBootstrapInfo ^∙ bsiLIWS ∙ liwsLedgerInfo ∙ liConsensusDataHash
            authorsMap      = vv ^∙ vvAddressToValidatorInfo
            authors         = kvm-toList authorsMap
            authorsIDs≢     = kvm-keys-All≢ authorsMap
            authorsInfo     = List-map proj₂ authors
            numAuthors      = length authors
            members         = allFin numAuthors
            qsize           = vv ^∙ vvQuorumVotingPower
            toNodeId        = proj₁ ∘ List-lookup authors
            getAuthorInfo   = proj₂ ∘ List-lookup authors
            getPubKey       = _^∙ vciPublicKey ∘ getAuthorInfo
            VotPowerMembers = f-sum (_^∙ vciVotingPower ∘ getAuthorInfo)
            VotPowerAuthors = f-sum (_^∙ vciVotingPower)
            bizF            = VotPowerAuthors authorsInfo ∸ qsize
            getAuthInfo≡VCI : List-map getAuthorInfo members ≡ authorsInfo
            getAuthInfo≡VCI = trans (List-map-compose members) (cong (List-map proj₂) (map-lookup-allFin authors))
            totalVotPower≡  : VotPowerAuthors authorsInfo ≡ VotPowerMembers members
            totalVotPower≡  = let sumf∘g = sum-f∘g members (_^∙ vciVotingPower) getAuthorInfo
                              in sym (trans sumf∘g (cong (f-sum (_^∙ vciVotingPower)) getAuthInfo≡VCI))
            N∸bizF≡Qsize    = subst ((_≡ qsize) ∘ (_∸ bizF)) totalVotPower≡ (m∸[m∸n]≡n ((proj₁ ∘ proj₂) ok))
            getPKey-Inj   : ∀ {m₁ m₂} → getPubKey m₁ ≡ getPubKey m₂ → m₁ ≡ m₂
            getPKey-Inj {m₁} {m₂} pk≡
              with m₁ ≟Fin m₂
            ...| yes m₁≡m₂ = m₁≡m₂
            ...| no  m₁≢m₂ = let nIdm₁≢nIdm₂ = allDistinct-Map {xs = authors} proj₁ authorsIDs≢ m₁≢m₂
                                 pksAll≢ = (proj₁ ∘ proj₂ ∘ proj₂) ok
                             in ⊥-elim (pksAll≢ (getAuthorInfo m₁) (getAuthorInfo m₂)
                                                (toNodeId m₁) (toNodeId m₂) nIdm₁≢nIdm₂
                                                (kvm-toList-lookup authorsMap) (kvm-toList-lookup authorsMap)
                                         pk≡)

postulate -- TODO-2: define BootstrapInfo to match implementation and write these functions
  init-EC : BootstrapInfo → EpochConfig

module WithEC (𝓔 : EpochConfig) where
  open EpochConfig 𝓔
  open WithAbsVote 𝓔

  -- A 'ConcreteVoteEvidence' is a piece of information that
  -- captures that the 'vd : AbsVoteData' in question was not /invented/
  -- but instead, comes from a concrete vote that is /valid/ (that is,
  -- signature has been checked and author belongs to this epoch).
  --
  -- Moreover, we will also store the RecordChain that leads to the vote;
  -- this requires some mutually-recursive shenanigans, so we first declare
  -- ConcreteVoteEvidence, then import the necessary modules, and then define it.
  record ConcreteVoteEvidence (vd : AbsVoteData) : Set

  open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 ConcreteVoteEvidence as Abs hiding (qcVotes; Vote)

  data VoteCoherence (v : Vote) (b : Abs.Block) : Set where
    initial  : v ^∙ vParentId    ≡ genesisUID
             → v ^∙ vParentRound ≡ 0
             → Abs.bPrevQC b     ≡ nothing
             → VoteCoherence v b

    ¬initial : ∀{b' q}
             → v ^∙ vParentId    ≢ genesisUID
             → v ^∙ vParentRound ≢ 0
             → v ^∙ vParentId    ≡ Abs.bId b'
             → v ^∙ vParentRound ≡ Abs.bRound b'
             → (Abs.B b') ← (Abs.Q q)
             → (Abs.Q q)  ← (Abs.B b)
             → VoteCoherence v b

  -- Estabilishing validity of a concrete vote involves checking:
  --
  --   i) Vote author belongs to the current epoch
  --  ii) Vote signature is correctly verified
  -- iii) Existence of a RecordChain up to the voted-for block.
  --  iv) Coherence of 'vdParent' field with the above record chain.
  --
  record IsValidVote (v : Vote) : Set where
    constructor IsValidVote∙new
    inductive
    field
      _ivvMember   : Member
      _ivvAuthor   : isMember? (_vAuthor v) ≡ just _ivvMember
      _ivvSigned   : WithVerSig (getPubKey _ivvMember) v

      _ivvVDhash   : v ^∙ vLedgerInfo ∙ liConsensusDataHash ≡ hashVD (v ^∙ vVoteData)

      -- A valid vote must vote for a block that exists and is
      -- inserted in a RecordChain.
      _ivvBlock    : Abs.Block
      _ivvBlockId  : v ^∙ vProposedId ≡ Abs.bId _ivvBlock

      -- Moreover; we must check that the 'parent' field of the vote is coherent.
      _ivvCoherent : VoteCoherence v _ivvBlock

      -- Finally, the vote is for the correct epoch
      _ivvEpoch    : v ^∙ vEpoch ≡ epoch
      _ivvEpoch2   : v ^∙ vParent ∙ biEpoch ≡ epoch  -- Not needed?
  open IsValidVote public

  -- A valid vote can be directly mapped to an AbsVoteData. Abstraction of QCs
  -- and blocks will be given in LibraBFT.Concrete.Records, since those are
  -- more involved functions.
  α-ValidVote : (v : Vote) → Member → AbsVoteData
  α-ValidVote v mbr = AbsVoteData∙new (v ^∙ vProposed ∙ biRound)
                                      mbr
                                      (v ^∙ vProposed ∙ biId)

  -- α-ValidVote is the same for two votes that have the same vAuthor, vdProposed and vOrder
  α-ValidVote-≡ : ∀ {cv v'} {m : Member}
                → _vdProposed (_vVoteData cv) ≡ _vdProposed (_vVoteData v')
                → α-ValidVote cv m ≡ α-ValidVote v' m
  α-ValidVote-≡ {cv} {v'} prop≡ =
    AbsVoteData-η (cong _biRound prop≡) refl (cong _biId prop≡)

  -- Finally; evidence for some abstract vote consists of a concrete valid vote
  -- that is coherent with the abstract vote data.
  record ConcreteVoteEvidence vd where
    constructor CVE∙new
    inductive
    field
      _cveVote        : Vote
      _cveIsValidVote : IsValidVote _cveVote
      _cveIsAbs       : α-ValidVote _cveVote (_ivvMember _cveIsValidVote) ≡ vd
  open ConcreteVoteEvidence public

  -- Gets the signature of a concrete vote evidence
  _cveSignature : ∀{vd} → ConcreteVoteEvidence vd → Signature
  _cveSignature = _vSignature ∘ _cveVote

  -- A valid quorum certificate contains a collection of valid votes, such that
  -- the members represented by those votes (which exist because the votes are valid)
  -- constitutes a quorum.
  record MetaIsValidQC (qc : QuorumCert) : Set where
    field
      _ivqcMetaVotesValid      : All (IsValidVote ∘ rebuildVote qc) (qcVotes qc)
      _ivqcMetaIsQuorum        : IsQuorum (All-reduce _ivvMember _ivqcMetaVotesValid)
  open MetaIsValidQC public

  -- A valid TimeoutCertificate has a quorum of signatures that are valid for the current
  -- EpochConfig.  There will be a lot of overlap with MetaIsValidQc and IsValidVote.
  -- TODO-2: flesh out the details.
  postulate
    MetaIsValidTimeoutCert : TimeoutCertificate → Set

  {-
  record MetaIsValidTimeoutCert (tc : TimeoutCertificate) : Set where
    field
      _ivtcMetaSigsValid :
      _ivtcMetaIsQuorum  : 
  -}

  vqcMember : (qc : QuorumCert) → MetaIsValidQC qc
             → ∀ {as} → as ∈ qcVotes qc → Member
  vqcMember qc v {α , _ , _} as∈qc with All-lookup (_ivqcMetaVotesValid v) as∈qc
  ...| prf = _ivvMember prf

