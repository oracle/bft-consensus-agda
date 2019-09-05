open import Prelude
open import BasicTypes
open import Hash

-- Here we provide abstract definitions of
-- verified records, that is, we assume that
-- they have been received through the wire and
-- validated accordingly. This include:
--
--  1) Well-formedness of different fields
--  2) Sender have been aute'ed against an epoch.
--  3) Signatures have been verified
-- 
module Abstract.Records {f : ℕ} (ec : EpochConfig f)  
  -- A Hash function maps a bytestring into a hash.
  (hash     : ByteString → Hash)
  -- And is colission resistant
  (hash-cr  : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  -- TODO: discuss if we want to keep signatures here.
  --  VCM: I'm leaning towards leaving signatures out and
  --       handlign these on the validation layer.

  -- MSM: these definitions are virtually identical to those that are included in the "concrete"
  -- model (such as it is, so far).  I see little to no advantage in duplicating these definitions,
  -- so I think we should just use the same definitions; that would imply including the signatures,
  -- even though we won't use them in the abstract (though conceibably we might in future, when
  -- considering accountability extensions)
  
  -- VCM && LPS: I think that the fact that we don't use the signature in the abstract
  --             model suggest we should keep the datatypes separate.
  --             Moreover, the fact that these types carry a number of 'aux' fields
  --             as mentioned below, will nevertheless require some function
  --             with type:
  --
  --               toAbstract :: SomeSystemState -> NetworkRecord -> Maybe Abstract.Record
  --               toAbstract st x = if signatureOk x then ... 
  --                                 if numberOfFieldsOk x then ...
  --                                 ...
  -- 
  --             Another reason for doing so really is lowering the burden to understanding 
  --             the abstract interface independently of the concrete model. The more unused 
  --             things we have here, the more room for error.
  

  record Block  : Set where
    constructor mkBlock
    field
      bAuthor     : Author ec
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
  open Block public 

  postulate
    _≟Block_ : (b₀ b₁ : Block) → Dec (b₀ ≡ b₁)

  record Vote  : Set where
    constructor mkVote
    field
      vAuthor    : Author ec
      vBlockHash : BlockHash
      vRound     : Round

      -- MSM: this is an "auxiliary" variable that would probably not be included in a real
      -- implementation (and is not included in the LibraBFT implementation we're modeling).  It's
      -- therefore critical that we ensure that nothing in the model of the algorithm uses it.  
      --  
      --     LPS && VCM: Indeed. I think that if we keep Abstract.Record and Concrete.Record
      --                 separate types, we are guaranted to never use it in the model of the algo.
      -- 
      -- I've been following a convenition of preceding all types and fields names with "Aux" or "aux" to
      -- make this easy to spot.  A related issue I mentioned before is whether we should include
      -- any aux fields in implementation types (as is done here with vOrder) or if we should have
      -- associated auxiliary types (e.g., AuxVote) to record Auxiliary information about the
      -- relevant implementation type (Vote, in this case). So far, I've preferred the latter
      -- approach.  Sometimes we may want to be able to respresent values that don't (yet) have
      -- associated auxiliary data or that don't satisfy the properties represented in the auxiliary
      -- data.  For example, a signed message the does not comply with protocol rules might be kept
      -- for accountability reasons.  Overall, I lean towards keeping abstract and implementation
      -- types identical, and keeping any auxiliary information such as vOrder, invariants, etc. in
      -- auxiliary types.
      --
      --    LPS && VCM: We think that this being under the Abstract folder should be enough 
      --                to make it clear that there are fields in these records used only
      --                to prove theorems. Again, it might pay off to keep implementation and
      --                model types separate. For example, the function that translates concrete 
      --                to abstract record will also work as a specification of what we are abstracting over.
      
      -- The 'vOrder' is a "metafield", it keeps track of which vote from 'vAuthor'
      -- this is representing. This makes it much simpler to talk about thinks such as 
      -- the increasing round rule. 
      vOrder     : ℕ 
      --vState     : State
      --vSignature : Signature
  open Vote public

  -- * Quorum Certificates
  --
  -- These are intersting. A Valid quorum certificate contains
  -- at least 'QuorumSize ec' votes from different authors.
  -- 
  -- We achive that by considering a sorted list of 'Vote's
  -- with the _<_ relation from Data.Fin, which also guarantees
  -- the authors are different. 

  -- Extends an arbitrary relation to work on the head of
  -- the supplied list, if any.
  data OnHead {A : Set}(P : A → A → Set) (x : A) : List A → Set where
    []  : OnHead P x []
    _∷_ : ∀{y ys} → P x y → OnHead P x (y ∷ ys)

  -- Estabilishes that a list is sorted according to the supplied
  -- relation.
  data IsSorted {A : Set}(_<_ : A → A → Set) : List A → Set where
    []  : IsSorted _<_ []
    _∷_ : ∀{x xs} → OnHead _<_ x xs → IsSorted _<_ xs → IsSorted _<_ (x ∷ xs)

  record QC : Set₁ where
    field
      qAuthor        : Author ec
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : List Vote
      -- MSM: Same comment as before: these fields should be clearly demarcated as "auxiliary"
      -- (see previous comments about prefix in name and/or separate type) 
      -- VCM && LPS: See above

      -- Here are the coherence conditions. Firstly, we expect
      -- 'qVotes' to be sorted, which guarnatees distinct authors.
      qVotes-C1      : IsSorted (λ v₀ v₁ → vAuthor v₀ <Fin vAuthor v₁) qVotes 
      -- Secondly, we expect it to have at least 'QuorumSize' number of
      -- votes, for the particular epoch in question.
      qVotes-C2      : QuorumSize ec ≤ length qVotes
      -- All the votes must vote for the qBlockHash in here;
      qVotes-C3      : All (λ v → vBlockHash v ≡ qBlockHash) qVotes
      -- Likewise for rounds
      qVotes-C4      : All (λ v → vRound v ≡ qRound) qVotes
  open QC public

  -- TODO:
  -- VCM: Lisandra notes that we might not need propositional equality on quorum certificates.
  -- I agree. We can define our own equivalence relation comparing the size of the list, the author,
  -- the round and the blockhash. We don't particuarly care about the votes!
  -- 
  -- For now, anyway, I'll just postulate decidable equality of what we currently have.
  postulate _≟QC_ : (q₀ q₁ : QC) → Dec (q₀ ≡ q₁)

  -- It's pretty easy to state whether an author has voted in
  -- a given QC.
  _∈QC_  : Author ec → QC → Set
  a ∈QC qc = Any (λ v → vAuthor v ≡ a) (qVotes qc)

  _∈QCv_ : Vote → QC → Set
  v ∈QCv qc = Any (λ v' → v' ≡ v) (qVotes qc)

  -- MSM: I understand we're abstracting from some mundane lookup function here,
  -- but don't we need some constraint on the vote it returns?  Couldn't it just
  -- return a random vote that's not by a and/or not in q?
  -- LPS && VCM: It is easier to add a correctness lemma, see below.

  -- TODO: gets the vote of a ∈QC -- TODO: make q explicit; a implicit
  ∈QC-Vote : ∀{q}(a : Author ec) → (a ∈QC q) → Vote
  ∈QC-Vote _ _ = magic
    where postulate magic : ∀{a}{A : Set a} → A
  
  ∈QC-Vote-correct : ∀ q → {a : Author ec} → (p : a ∈QC q) 
                   → (∈QC-Vote {q} a p) ∈QCv q
  ∈QC-Vote-correct = magic
    where postulate magic : ∀{a}{A : Set a} → A

  -- The initial record is unique per epoch. Essentially, we just
  -- use the 'epochSeed' and the hash of the last record of the previous
  -- epoch to piggyback the initial record.
  data Initial : Set where
    mkInitial : Initial

  -- TODO: We are not handling timeouts yet
  record Timeout : Set where
    constructor mkTimeout
    field
      toAuthor  : Author ec
      toRound   : Round
      --toSignature : Signature
  open Timeout public

  -- A record is defined by being either of the types introduced above.
  data Record : Set₁ where
    I : Initial   → Record
    B : Block     → Record
    Q : QC        → Record
    -- V : Vote      → Record
    -- T : Timeout   → Record

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  -- Each record has a round
  round : Record → Round
  round (I i) = 0
  round (B b) = bRound b
  round (Q q) = qRound q
  -- round (V v) = vRound v
  -- round (T t) = toRound t

  -- We need to encode records into bytestrings in order to hash them.
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR : Record → Hash
  HashR = hash ∘ encodeR

  data _←_ : Record → Record → Set where
    I←B : {i : Initial} {b : Block}
          → HashR (I i) ≡  bPrevQCHash b
          → I i ← B b
    Q←B : {q : QC} {b : Block}
          → HashR (Q q) ≡  bPrevQCHash b
          → Q q ← B b
    B←Q : {b : Block} {q : QC}
          → HashR (B b) ≡ qBlockHash q
          → B b ← Q q
    -- B←V : {b : Block} {v : Vote}
    --       → HashR (B b) ≡ vBlockHash v
    --       → B b ← V v

