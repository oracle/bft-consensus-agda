{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Hash
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Consensus.Types.EpochIndep

-- This module postulates a collision-resistant cryptographic hash
-- function (we call it sha256 for concreteness, but it could be any
-- collision-resistant cryptographic hash function), and defines hash
-- functions used in (an earlier version of) LibraBFT, properties
-- about it, and how Votes and Blocks are signed.

module LibraBFT.Impl.Util.Crypto where
  -- Note that this is an abstraction of a collision-resistant hash function.  It could be any such
  -- hash function, not necessarily sha256.  We just call it sha256 for "concreteness", to remind
  -- ourselves it's modeling such a function.
  postulate -- valid assumption (collision-resistant hash function)
    sha256    : BitString → Hash
    sha256-cr : ∀{x y} → sha256 x ≡ sha256 y → Collision sha256 x y ⊎ x ≡ y

  open WithCryptoHash sha256 sha256-cr

  blockInfoBSList : BlockInfo → List ByteString
  blockInfoBSList (mkBlockInfo epoch round id) = encode epoch ∷ encode round ∷ encode id ∷ []

  hashBI : BlockInfo → HashValue
  hashBI = sha256 ∘ bs-concat ∘ blockInfoBSList

  hashBI-inj : ∀ {bi1 bi2} → hashBI bi1 ≡ hashBI bi2 → NonInjective-≡ sha256 ⊎ bi1 ≡ bi2
  hashBI-inj {bi1} {bi2} hyp with sha256-cr hyp
  ...| inj₁ col = inj₁ (_ , col)
  ...| inj₂ res with bs-concat-inj (blockInfoBSList bi1) (blockInfoBSList bi2) res
  ...| final = inj₂ (BlockInfo-η (encode-inj (proj₁ (∷-injective final)))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective final)))))
                                 (encode-inj (proj₁ (∷-injective (proj₂ (∷-injective (proj₂ (∷-injective final))))))))

  voteDataHashList : VoteData → List Hash
  voteDataHashList (mkVoteData proposed parent) =
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

  hashLI : LedgerInfo → HashValue
  hashLI (mkLedgerInfo commitInfo consensusDataHash) =
    hash-concat (hashBI commitInfo ∷ consensusDataHash ∷ [])

  hashLI-inj : ∀ {li1 li2} → hashLI li1 ≡ hashLI li2 → NonInjective-≡ sha256 ⊎ li1 ≡ li2
  hashLI-inj {mkLedgerInfo ci1 cd1} {mkLedgerInfo ci2 cd2} prf
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

  constructLI : Vote → LedgerInfo
  constructLI v = mkLedgerInfo (₋liCommitInfo (₋vLedgerInfo v)) (hashVD (₋vVoteData v))

  hashVote : Vote → HashValue
  hashVote = hashLI ∘ constructLI

  hashVote-inj1 : ∀ {v1 v2} → hashVote v1 ≡ hashVote v2
                → NonInjective-≡ sha256 ⊎ ₋vVoteData v1 ≡ ₋vVoteData v2
  hashVote-inj1 {v1} {v2} hyp with hashLI-inj {constructLI v1} {constructLI v2} hyp
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ ok = hashVD-inj {₋vVoteData v1} {₋vVoteData v2} (cong ₋liConsensusDataHash ok)

  -- A vote is always signed; as seen by the 'Unit'
  -- in the definition of Signed.
  instance
    sig-Vote : WithSig Vote
    sig-Vote = record
       { Signed         = λ _ → Unit
       ; Signed-pi      = λ _ _ _ → Unit-pi
       ; isSigned?      = λ _ → yes unit
       ; signature      = λ v _ → ₋vSignature v
       ; signableFields = encodeH ∘ hashVote
       }

  -- Captures a proof that a vote was cast by α by recording that 'verify' returns true.
  VoteSigVerifies : PK → Vote → Set
  VoteSigVerifies pk v = T (verify (signableFields ⦃ sig-Vote ⦄ v) (₋vSignature v) pk)

  Signed-pi-Blk : (b : Block)
                → (is1 is2 : (Is-just ∘ ₋bSignature) b)
                → is1 ≡ is2
  Signed-pi-Blk (mkBlock _ _ .(just _)) (just _) (just _) = cong just refl

  -- A Block might carry a signature
  instance
    sig-Block : WithSig Block
    sig-Block = record
       { Signed         = Is-just ∘ ₋bSignature
       ; Signed-pi      = Signed-pi-Blk
       ; isSigned?      = λ b → Maybe-Any-dec (λ _ → yes tt) (b ^∙ bSignature)
       ; signature      = λ { _ prf → to-witness prf }
       ; signableFields = λ b → concat (encodeH (₋bId b) ∷ encode (b ^∙ bBlockData) ∷ [])
       }
