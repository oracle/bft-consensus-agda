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

  -- Accessing the fields start to be a nuissance; yet, Blocks,
  -- votes and QC's all have three important common fields: author, round and prevHash.
  -- I'll make the same trick as Harold and declare a type-class that gives
  -- the getters for the stuff we need all the time.
  record IsLibraBFTRecord (A : Set) : Set where
    constructor is-librabft-record
    field
      getAuthor   : A → Author ec
      getRound    : A → Round
      getPrevHash : A → Hash
      getEpochId  : A → EpochId
  open IsLibraBFTRecord {{...}} public

  -- I'm postulating this instance here instead of
  -- at Base.Types because here this is for a specific ec;
  -- If we postulate it there, we'll run into multiple unsolvd metas.
  postulate
   instance encAuthors : Encoder (Author ec)

  Block : Set
  Block = VerSigned (BBlock (Author ec))

  instance
    block-is-record : IsLibraBFTRecord Block
    block-is-record = is-librabft-record 
      (bAuthor ∘ content) 
      (bRound ∘ content) 
      (bPrevQCHash ∘ content) 
      (bEpochId ∘ content)

  -- TODO: Implement
  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  -- VCM: We now have the hability to define vOrder
  -- only here and remove it from BVote; this would mean
  -- that the concrete interface doesn't see it; and we just 
  -- postulate the hability to create a vOrder.
  Vote : Set
  Vote = VerSigned (BVote (Author ec))

  voteOrder : Vote → VoteOrder
  voteOrder = vOrder ∘ content
    
  instance
    vote-is-record : IsLibraBFTRecord Vote
    vote-is-record = is-librabft-record 
      (vAuthor ∘ content) 
      (vRound ∘ content) 
      (vBlockHash ∘ content)
      (vEpochId ∘ content)


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
      qVotes-C1      : IsSorted (λ v₀ v₁ → getAuthor v₀ <Fin getAuthor v₁) 
                                (qVotes (content qBase)) 
      -- Secondly, we expect it to have at least 'QuorumSize' number of
      -- votes, for the particular epoch in question.
      qVotes-C2      : QuorumSize ec ≤ length (qVotes (content qBase))
      -- All the votes must vote for the qBlockHash in here;
      qVotes-C3      : All (λ v → getPrevHash v ≡ qBlockHash (content qBase)) 
                           (qVotes (content qBase))
      -- Likewise for rounds
      qVotes-C4      : All (λ v → getRound v ≡ qRound (content qBase)) (qVotes (content qBase))
  open QC public

  -- Accessors

  qcVotes : QC → List Vote
  qcVotes = qVotes ∘ content ∘ qBase

  instance 
    qc-is-record : IsLibraBFTRecord QC
    qc-is-record = is-librabft-record 
      (qAuthor ∘ content ∘ qBase) 
      (qRound ∘ content ∘ qBase) 
      (qBlockHash ∘ content ∘ qBase)
      (qEpochId ∘ content ∘ qBase)

  Commit : Set
  Commit = VerSigned (BC (Author ec))

  instance
    commit-is-record : IsLibraBFTRecord Commit
    commit-is-record = is-librabft-record
      (cAuthor ∘ content)
      (cRound ∘ content)
      (cCert ∘ content)
      (cEpochId ∘ content)

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
  a ∈QC qc = Any (λ v → getAuthor v ≡ a) (qcVotes qc)

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{a : Author ec} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q


  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qcVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- A record is defined by being either of the types introduced above.
  --
  -- VCM: TODO: Shouldn't we take the new BlockStore
  -- approach and couple blocks and QCs on the same datatype?
  -- Yes, its a major effort, but I believe it will pay off
  -- in helping to distinguish network records from records supposed
  -- to be stored in the block store.
  data Record : Set where
    I : Initial   → Record
    B : Block     → Record
    Q : QC        → Record
    -- VCM: I think these should never be made records!
    --      Records are meant to be put on the RecordStore (a.k.a block store)
    --      tiemouts and votes are 'messages'; that is, they are transfered
    --      from partciant to participand but don't go into the store.
    -- V : Vote      → Record
    -- T : Timeout   → Record

  B≢Q : ∀{b q} → B b ≡ Q q → ⊥
  B≢Q ()

  Q-injective : ∀{q q'} → Q q ≡ Q q' → q ≡ q'
  Q-injective refl = refl

  -- VCM: LibraBFT.Abstract.Record.Extends.HashR, which hashes
  --      a record, is defined in terms of this encoder.
  --      This is why we explicitely REMOVE the signature from
  --      this bytestring or define HashR differently.
  --      The end of Section 4.1 (libra v1 paper) indicates 
  --      signatures are /not/ part of the hash of records.
  --
  --      Nevertheless, Record's are not supposed to be sent
  --      over the wire; LibraBFT.Concrete.RecordStoreState.VerNetworkRecords
  --      serve that purpose.      
  instance
   encRecord : Encoder Record
   encRecord = record 
     { encode     = enc1 
     ; encode-inj = λ {r} {s} → enc1-inj r s 
     } where
       enc1 : Record → ByteString
       enc1 (I _) = false ∷ false ∷ [] ++ encode (seed ec) ++ encode (epochId ec)
       enc1 (B x) = true  ∷ false ∷ encode (content x)
       enc1 (Q x) = false ∷ true  ∷ encode (content (qBase x))

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
  round (B b) = getRound b
  round (Q q) = getRound q
  -- round (V v) = vRound v 
  -- round (T t) = toRound t

