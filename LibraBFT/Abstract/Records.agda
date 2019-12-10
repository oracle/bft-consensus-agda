open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Hash

open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- Here we provide abstract definitions of
-- verified records, that is, we assume that
-- they have been received through the wire and
-- validated accordingly. This include:
--
--  1) Well-formedness of different fields
--  2) Sender have been aute'ed against an epoch.
--  3) Signatures have been verified
-- 
-- This module does not bring in the hashing functionality
-- because we'd like to keep dependencies separate. 
-- The extends relation, _←_, is in LibraBFT.Abstract.Records.Extends
--
module LibraBFT.Abstract.Records (ec : EpochConfig) where

  postulate 
   instance
    encBBlock : Encoder (BBlock (Author ec))
    encBVote  : Encoder (BVote  (Author ec))
    encBQC    : ∀{V}⦃ encV : Encoder V ⦄ → Encoder (BQC (Author ec) V)

  Block : Set
  Block = VerSigned (BBlock (Author ec))

  blockRound : Block → Round
  blockRound = bRound ∘ content

  blockPrev  : Block → QCHash
  blockPrev  = bPrevQCHash ∘ content
  
  -- TODO: Implement
  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  Vote : Set
  Vote = VerSigned (BVote (Author ec))

  voteAuthor : Vote → Author ec
  voteAuthor = vAuthor ∘ content

  voteBlockHash : Vote → BlockHash
  voteBlockHash = vBlockHash ∘ content

  voteRound : Vote → Round
  voteRound = vRound ∘ content

  voteOrder : Vote → ℕ
  voteOrder = vOrder ∘ content
 
  -- * Quorum Certificates
  --
  -- These are intersting. A Valid quorum certificate contains
  -- at least 'QuorumSize ec' votes from different authors.
  -- 
  -- We achive that by considering a sorted list of 'Vote's
  -- with the _<_ relation from Data.Fin, which also guarantees
  -- the authors are different. 
  record QC : Set where
    field
      qBase          : VerSigned (BQC (Author ec) Vote)
      -- Here are the coherence conditions. Firstly, we expect
      -- 'qVotes' to be sorted, which guarnatees distinct authors.
      qVotes-C1      : IsSorted (λ v₀ v₁ → voteAuthor v₀ <Fin voteAuthor v₁) 
                                (qVotes (content qBase)) 
      -- Secondly, we expect it to have at least 'QuorumSize' number of
      -- votes, for the particular epoch in question.
      qVotes-C2      : QuorumSize ec ≤ length (qVotes (content qBase))
      -- All the votes must vote for the qBlockHash in here;
      qVotes-C3      : All (λ v → voteBlockHash v ≡ qBlockHash (content qBase)) 
                           (qVotes (content qBase))
      -- Likewise for rounds
      qVotes-C4      : All (λ v → voteRound v ≡ qRound (content qBase)) (qVotes (content qBase))
  open QC public

  qcRound : QC → Round
  qcRound = qRound ∘ content ∘ qBase

  qcAuthor : QC → Author ec
  qcAuthor = qAuthor ∘ content ∘ qBase

  qcVotes : QC → List Vote
  qcVotes = qVotes ∘ content ∘ qBase

  qcBlockHash : QC → BlockHash
  qcBlockHash = qBlockHash ∘ content ∘ qBase

  -- TODO:
  -- VCM: Lisandra notes that we might not need propositional equality on quorum certificates.
  -- I agree. We can define our own equivalence relation comparing the size of the list, the author,
  -- the round and the blockhash. We don't particuarly care about the votes!
  -- 
  -- For now, anyway, I'll just postulate decidable equality of what we currently have.
  postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

  Timeout : Set
  Timeout = BTimeout (Author ec)

  -- It's pretty easy to state whether an author has voted in
  -- a given QC.
  _∈QC_  : Author ec → QC → Set
  a ∈QC qc = Any (λ v → voteAuthor v ≡ a) (qcVotes qc)

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{a : Author ec} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q


  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qcVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- A record is defined by being either of the types introduced above.
  data Record : Set where
    I : Initial   → Record
    B : Block     → Record
    Q : QC        → Record
    -- V : Vote      → Record
    -- T : Timeout   → Record

  B≢Q : ∀{b q} → B b ≡ Q q → ⊥
  B≢Q ()

  Q-injective : ∀{q q'} → Q q ≡ Q q' → q ≡ q'
  Q-injective refl = refl

  instance
   encRecord : Encoder Record
   encRecord = record 
     { encode     = enc1 
     ; encode-inj = λ {r} {s} → enc1-inj r s 
     } where
       enc1 : Record → ByteString
       enc1 (I _) = false ∷ false ∷ [] ++ encode (seed ec) ++ encode (epochId ec)
       enc1 (B x) = true  ∷ false ∷ encode x 
       enc1 (Q x) = false ∷ true  ∷ encode (qBase x)

       postulate magic : ∀{a}{A : Set a} → A

       -- TODO: Implement this later; The important bit
       --       is that Agda easily understands that the type tags
       --       work and discharges the difficult cases. 
       --       Although long; the proof for QC will be boring; I already
       --       proved the bits and pieces proof irrelevant in Lemmas.
       enc1-inj : ∀ r s → enc1 r ≡ enc1 s → r ≡ s
       enc1-inj (I x) (I x₁) hyp = magic
       enc1-inj (B x) (B x₁) hyp = magic
       enc1-inj (Q x) (Q x₁) hyp = magic
       enc1-inj (I x) (B x₁) ()
       enc1-inj (I x) (Q x₁) ()
       enc1-inj (B x) (I x₁) ()
       enc1-inj (B x) (Q x₁) ()
       enc1-inj (Q x) (I x₁) ()
       enc1-inj (Q x) (B x₁) ()

  -- Now, the encodings we had as postulates
  -- back in LibraBFT.Abstract.Record.Extends we can
  -- define as first class citizens
  encodeR : Record → ByteString
  encodeR = encode 

  encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)
  encodeR-inj = encode-inj

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  -- Each record has a round
  round : Record → Round
  round (I i) = 0
  round (B b) = blockRound b
  round (Q q) = qcRound q
  -- round (V v) = vRound v 
  -- round (T t) = toRound t
