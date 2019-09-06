{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

-- Here we provide abstract definitions of
-- verified records, that is, we assume that
-- they have been received through the wire and
-- validated accordingly. This include:
--
--  1) Well-formedness of different fields
--  2) Sender have been aute'ed against an epoch.
--  3) Signatures have been verified
-- 
-- This module does not brings in the hashing functionality
-- because we'd like to keep dependencies separate. 
-- The rextends relaion, _←_, is in LibraBFT.Abstract.Records.Extends
--
module LibraBFT.Concrete.Records 
 where

  -- The concrete model will be receiving signed records.
  -- They all share the same fields: they come from a node that 
  -- produce some content and signed it. Upon validation
  -- with a given concrete ' ec : EpochConfig', we should be able to
  -- produce a 'Author ec' and view the signed content as an 
  -- abstract record.
  record Signed {A : Set} : Set where
    constructor signed
    field
      sAuthor     : NodeId
      sContent    : A
      sSignature  : Signature
  open Signed public

  record Block  : Set where
    constructor mkBlock
    field
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
  open Block public 

  record Vote  : Set where
    constructor mkVote
    field
      vBlockHash : BlockHash
      vRound     : Round
      -- TODO: What to do with the concrete vOrder?
      vOrder     : ℕ 
      --vState     : State
  open Vote public

  record QC : Set where
    field
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : List Vote
  open QC public

  data Record : Set where
    B : Block     → Record
    Q : QC        → Record
    -- V : Vote      → Record
    -- T : Timeout   → Record



{-
  -- TODO: Implement
  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  -- * Quorum Certificates
  --
  -- These are intersting. A Valid quorum certificate contains
  -- at least 'QuorumSize ec' votes from different authors.
  -- 
  -- We achive that by considering a sorted list of 'Vote's
  -- with the _<_ relation from Data.Fin, which also guarantees
  -- the authors are different. 

  -- TODO:
  -- VCM: Lisandra notes that we might not need propositional equality on quorum certificates.
  -- I agree. We can define our own equivalence relation comparing the size of the list, the author,
  -- the round and the blockhash. We don't particuarly care about the votes!
  -- 
  -- For now, anyway, I'll just postulate decidable equality of what we currently have.
  postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

  -- TODO: We are not handling timeouts yet
  record Timeout : Set where
    constructor mkTimeout
    field
      toAuthor  : Author ec
      toRound   : Round
  open Timeout public

  -- It's pretty easy to state whether an author has voted in
  -- a given QC.
  _∈QC_  : Author ec → QC → Set
  a ∈QC qc = Any (λ v → vAuthor v ≡ a) (qVotes qc)

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{a : Author ec} (q : QC) → (a ∈QC q) → Vote
  ∈QC-Vote q a∈q = Any-lookup a∈q


  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q)
                   → (∈QC-Vote {a} q p) ∈ qVotes q
  ∈QC-Vote-correct q a∈q = Any-lookup-correct a∈q

  -- A record is defined by being either of the types introduced above.
  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  -- Each record has a round
  round : Record → Round
  round (I i) = 0
  round (B b) = bRound b
  round (Q q) = qRound q
  -- round (V v) = vRound v
  -- round (T t) = toRound t
-}
