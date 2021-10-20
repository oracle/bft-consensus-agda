{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

-- This module postulates a collision-resistant cryptographic hash
-- function (we call it sha256 for concreteness, but it could be any
-- collision-resistant cryptographic hash function), and defines hash
-- functions used in (an earlier version of) LibraBFT, properties
-- about it, and how Votes and Blocks are signed.

module LibraBFT.ImplShared.Util.Crypto where
  -- Note that this is an abstraction of a hash function.  It could be any such hash function, not
  -- necessarily sha256.  We just call it sha256 for "concreteness", to remind ourselves it's
  -- modeling such a function.
  postulate -- valid assumption (hash function)
    sha256    : BitString → Hash

  -- For two values x and y, if their hashes are equal, then either there is a hash collision, or x
  -- and y are equal.
  sha256-cr : ∀{x y} → sha256 x ≡ sha256 y → Collision sha256 x y ⊎ x ≡ y
  sha256-cr {x} {y} hyp
     with x ≟BitString y
  ...| no  col  = inj₁ (col , hyp)
  ...| yes refl = inj₂ refl

  open WithCryptoHash sha256 sha256-cr

  -- We do not yet have sufficient support to model precisely the hashing used in the Haskell code,
  -- so it is better that we postulate its intended properties to ensure proofs have the desired
  -- properties available.  Note that a simpler injectivity property such as
  --
  -- hashBD-inj' : ∀ {bd1} {bd2}
  --             → hashBD bd1 ≡ hashBD bd2
  --             → NonInjective-≡ sha256
  --             ⊎ bd1 ≡L bd2
  --
  -- does *not* hold because the input to the hash function used in hashBD does *not* include all
  -- components of the BlockData being hashed.

  -- TODO-2: Similarly express other hashing functions and their intended injectivity properties where
  -- the Agda implementation does not accurately reflect the Haskell implementation.

  -- TODO-2: Enable support for the hashS function we use in the Haskell code, which hashes tuples
  -- of serializable types), and then define hashBD using this and prove that it ensures hashBD-inj.
  -- Note also the TODO below related to HashTags.

  record _BlockDataInjectivityProps_ (bd1 bd2 : BlockData) : Set where
    constructor mkBdInjProps
    field
      bdInjEpoch  : bd1 ≡L bd2 at bdEpoch
      bdInjRound  : bd1 ≡L bd2 at bdRound
      bdInjVD     : bd1 ≡L bd2 at (bdQuorumCert ∙ qcVoteData)
      bdInjLI     : bd1 ≡L bd2 at (bdQuorumCert ∙ qcSignedLedgerInfo ∙ liwsLedgerInfo)
      bdInjBTNil  : bd1 ^∙ bdBlockType ≡ NilBlock → bd2 ^∙ bdBlockType ≡ NilBlock
      bdInjBTGen  : bd1 ^∙ bdBlockType ≡ Genesis  → bd2 ^∙ bdBlockType ≡ Genesis
      bdInjBTProp : ∀ {tx}{auth} → bd1 ^∙ bdBlockType ≡ Proposal tx auth
                                 → bd1 ^∙ bdBlockType ≡ bd2 ^∙ bdBlockType
  open _BlockDataInjectivityProps_

  sameBlockData⇒≈ : ∀ {b1 b2}
                    → b1 ^∙ bId ≡ b2 ^∙ bId
                    → (b1 ^∙ bBlockData) BlockDataInjectivityProps (b2 ^∙ bBlockData)
                    → b1 ≈Block b2
  sameBlockData⇒≈ {b1} {b2} refl (mkBdInjProps refl refl refl refl nil gen prop)
     with b1 ^∙ bBlockData ∙ bdBlockType
  ...| NilBlock         rewrite nil  refl = refl
  ...| Genesis          rewrite gen  refl = refl
  ...| Proposal tx auth rewrite prop refl = refl

  BSL : Set
  BSL = List ByteString

  _≟-BSL_ : ∀ (bsl1 bsl2 : List ByteString) → Dec (bsl1 ≡ bsl2)
  _≟-BSL_ = List-≡-dec _≟ByteString_

  hashBSL = sha256 ∘ bs-concat

  postulate
    blockData-bsl     : BlockData → List ByteString

  hashBD : BlockData → HashValue
  hashBD = hashBSL ∘ blockData-bsl

  Injective-BlockData : Set
  Injective-BlockData = Injective-int _BlockDataInjectivityProps_ hashBSL blockData-bsl blockData-bsl

  -- TODO-1: prove it using bs-concat-inj
  postulate
    hashBD-inj : Injective-BlockData

  hashBlock : Block → HashValue
  hashBlock = hashBD ∘ (_^∙ bBlockData)

  blockInfoBSList : BlockInfo → List ByteString
  blockInfoBSList (BlockInfo∙new epoch round id execStId ver mes) =
    encode epoch ∷ encode round ∷ encode id ∷ encode execStId ∷ encode ver ∷ encode mes ∷ []

  hashBI : BlockInfo → HashValue
  hashBI = sha256 ∘ bs-concat ∘ blockInfoBSList

  hashBI-inj : ∀ {bi1 bi2} → hashBI bi1 ≡ hashBI bi2 → NonInjective-≡ sha256 ⊎ bi1 ≡ bi2
  hashBI-inj {bi1} {bi2} hyp with sha256-cr hyp
  ...| inj₁ col = inj₁ (_ , col)
  ...| inj₂ res with bs-concat-inj (blockInfoBSList bi1) (blockInfoBSList bi2) res
  ...| final = inj₂ (BlockInfo-η (encode-inj (proj₁ (∷-injective final)))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective final)))))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective final)))))))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective final)))))))))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective final)))))))))))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective final))))))))))))))

  voteDataHashList : VoteData → List Hash
  voteDataHashList (VoteData∙new proposed parent) =
    hProposed ∷ hParent ∷ []
   where
    hProposed = hashBI proposed
    hParent   = hashBI parent

  hashVD : VoteData → HashValue
  hashVD = hash-concat ∘ voteDataHashList

  VoteData-≢-eid : ∀ {vd1 vd2 : VoteData}
                 → vd1 ^∙ vdProposed ∙ biEpoch ≢ vd2 ^∙ vdProposed ∙ biEpoch
                 → vd1 ≢ vd2
  VoteData-≢-eid neq = λ x → neq (cong (_^∙ vdProposed ∙ biEpoch) x)

  VoteData-hb : ∀ {vd1 vd2 : VoteData}
              → vd1 ^∙ vdProposed ∙ biEpoch ≢ vd2 ^∙ vdProposed ∙ biEpoch
              → hashVD vd1 ≡ hashVD vd2
              → NonInjective-≡ sha256
  VoteData-hb {vd1} {vd2} neq hvd≡
    with hash-concat-inj {voteDataHashList vd1} {voteDataHashList vd2} hvd≡
  ...| inj₁ hb = hb
  ...| inj₂ xxx
     with cong head xxx
  ...| yyy
     with cong tail xxx
  ...| yyy'
     with cong head (just-injective yyy')
  ...| yyy''
     with just-injective yyy | just-injective yyy''
  ...| zzz | zzz'
     with hashBI-inj {vd1 ^∙ vdProposed} {vd2 ^∙ vdProposed} zzz |
          hashBI-inj {vd1 ^∙ vdParent}   {vd2 ^∙ vdParent}   zzz'
  ...| inj₁ hb  | _         = hb
  ...| inj₂ _   | inj₁ hb   = hb
  ...| inj₂ aaa | inj₂ aaa' = ⊥-elim (VoteData-≢-eid {vd1} {vd2} neq (VoteData-η aaa aaa'))

  hashVD-inj : ∀ {vd1 vd2} → hashVD vd1 ≡ hashVD vd2 → NonInjective-≡ sha256 ⊎ vd1 ≡ vd2
  hashVD-inj {vd1} {vd2} prf
    with hash-concat-inj {voteDataHashList vd1} {voteDataHashList vd2} prf
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ vdLists≡
     with hashBI-inj (proj₁ (∷-injective vdLists≡)) | hashBI-inj (proj₁ (∷-injective (proj₂ (∷-injective vdLists≡))))
  ...| inj₁ hb    | _         = inj₁ hb
  ...| inj₂ _     | inj₁ hb   = inj₁ hb
  ...| inj₂ prop≡ | inj₂ par≡ = inj₂ (VoteData-η prop≡ par≡)


  -- The Haskell implementation includes "HashTag"s when hashing in order to ensure that it is not
  -- possible (modulo hash collisions) for the encodings of two values of different types (e.g.,
  -- Vote and Block) to yield the same bitstring and thus the same hash (and therefore potentially
  -- the same signature, where hashes are signed).  For example, the Haskell hashLI function is:
  --
  -- hashLI :: LedgerInfo -> HashValue
  -- hashLI (LedgerInfo commitInfo (HashValue consensusDataHash)) =
  --   hashS (HLI, biParts commitInfo, consensusDataHash)
  --
  -- Note the HashTag HLI, which is not yet reflected in the Agda implementation.
  -- TODO-2: include HashTags in hash functions, consistent with the Haskell code.
  --
  -- As an aside, it is not clear whether these HashTags are necessary for all of the "inner"
  -- hashes.  They are needed to ensure that, for example, a dishonest peer cannot notice that the
  -- bits signed for a Vote happen to decode to a valid Block, and therefore take a Vote signature
  -- and use it to masquerade as a Block signture.  However, the implementation does include
  -- HashTags at each level, so we should too unless and until that changes.  
  hashLI : LedgerInfo → HashValue
  hashLI (LedgerInfo∙new commitInfo consensusDataHash) =
    hash-concat (hashBI commitInfo ∷ consensusDataHash ∷ [])

  hashLI-inj : ∀ {li1 li2} → hashLI li1 ≡ hashLI li2 → NonInjective-≡ sha256 ⊎ li1 ≡ li2
  hashLI-inj {LedgerInfo∙new ci1 cd1} {LedgerInfo∙new ci2 cd2} prf
     with hash-concat-inj {hashBI ci1 ∷ cd1 ∷ []} {hashBI ci2 ∷ cd2 ∷ []} prf
  ...| inj₁ hb      = inj₁ hb
  ...| inj₂ li1≡li2
     with ∷-injective li1≡li2
  ...| ci≡ , rest≡
     with ∷-injective rest≡
  ...| cdh≡ , _
     with hashBI-inj ci≡
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ cis≡
     = inj₂ (LedgerInfo-η cis≡ cdh≡)

  record Ledger2WaypointConverterInjectivityProps (l1 l2 : Ledger2WaypointConverter) : Set where
    {- TODO-2 : implement Ledger2WaypointConverterInjectivityProps
    field
      l2wcInjEpoch          : ?
      l2wcInjRootHash       : ?
      l2wcInjVersion        : ?
      --timestamp
      l2wcInjNextEpochState : ?
    -}
  postulate
    hashL2WC     : Ledger2WaypointConverter → HashValue
    hashL2WC-inj : ∀ {l1 l2}
                 → hashL2WC l1 ≡ hashL2WC l2
                 → NonInjective-≡ sha256 ⊎ Ledger2WaypointConverterInjectivityProps l1 l2

  constructLI : Vote → LedgerInfo
  constructLI v = LedgerInfo∙new (_liCommitInfo (_vLedgerInfo v)) (hashVD (_vVoteData v))

  hashVote : Vote → HashValue
  hashVote = hashLI ∘ constructLI

  hashVote-inj1 : ∀ {v1 v2} → hashVote v1 ≡ hashVote v2
                → NonInjective-≡ sha256 ⊎ _vVoteData v1 ≡ _vVoteData v2
  hashVote-inj1 {v1} {v2} hyp with hashLI-inj {constructLI v1} {constructLI v2} hyp
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ ok = hashVD-inj {_vVoteData v1} {_vVoteData v2} (cong _liConsensusDataHash ok)

  -- A vote is always signed; as seen by the 'Unit'
  -- in the definition of Signed.
  instance
    sig-Vote : WithSig Vote
    sig-Vote = record
       { Signed         = λ _ → Unit
       ; Signed-pi      = λ _ _ _ → Unit-pi
       ; isSigned?      = λ _ → yes unit
       ; signature      = λ v _ → _vSignature v
       ; signableFields = encodeH ∘ hashVote
       }

  sameSig⇒sameVoteData : ∀ {v1 v2 : Vote} {pk}
                       → WithVerSig pk v1
                       → WithVerSig pk v2
                       → v1 ^∙ vSignature ≡ v2 ^∙ vSignature
                       → NonInjective-≡ sha256 ⊎ v2 ^∙ vVoteData ≡ v1 ^∙ vVoteData
  sameSig⇒sameVoteData {v1} {v2} wvs1 wvs2 refl
     with verify-bs-inj (verified wvs1) (verified wvs2)
       -- The signable fields of the votes must be the same (we do not model signature collisions)
  ...| bs≡
       -- Therefore the LedgerInfo is the same for the new vote as for the previous vote
       = sym <⊎$> (hashVote-inj1 {v1} {v2} (sameBS⇒sameHash bs≡))

  -- Captures a proof that a vote was cast by α by recording that 'verify' returns true.
  VoteSigVerifies : PK → Vote → Set
  VoteSigVerifies pk v = T (verify (signableFields ⦃ sig-Vote ⦄ v) (_vSignature v) pk)

  Signed-pi-Blk : (b : Block)
                → (is1 is2 : (Is-just ∘ _bSignature) b)
                → is1 ≡ is2
  Signed-pi-Blk (Block∙new _ _ .(just _)) (just _) (just _) = cong just refl

  -- A Block might carry a signature
  instance
    sig-Block : WithSig Block
    sig-Block = record
       { Signed         = Is-just ∘ _bSignature
       ; Signed-pi      = Signed-pi-Blk
       ; isSigned?      = λ b → Maybe-Any-dec (λ _ → yes tt) (b ^∙ bSignature)
       ; signature      = λ { _ prf → to-witness prf }
       ; signableFields = λ b → concat (encodeH (_bId b) ∷ encode (b ^∙ bBlockData) ∷ [])
       }
