open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- Exposition of the ground types that we build our abstract reasoning
-- over. 
module LibraBFT.Base.Types where

  EpochId : Set
  EpochId = ℕ

  -- A node is a participant in the system. 
  NodeId : Set
  NodeId = ℕ

  Round : Set
  Round = ℕ

  Command : Set
  Command = ℕ

  QCHash : Set
  QCHash = Hash

  BlockHash : Set
  BlockHash = Hash

  State : Set
  State = Hash

  -- VCM: After our discussion about vote order; I propose
  -- we make it into a postulate. Naturally, as the name suggests,
  -- it must have some sort of order raltion; also inacessible.
  postulate
    VoteOrder : Set
    _<VO_     : VoteOrder → VoteOrder → Set

  -- An 'EpochConfig f' carries the information we need tot
  -- survive at most 'f' byzantine failures. for now, this is
  -- only a lower bound on the number of overal authors.
  record EpochConfig : Set where
    field
      epochId  : EpochId
      authorsN : ℕ
      bizF     : ℕ

      isBFT    : authorsN ≥ suc (3 * bizF)

      seed     : ℕ

      ecInitialState  : State

    QuorumSize : ℕ
    QuorumSize = authorsN ∸ bizF

    Author     : Set
    Author     = Fin authorsN

    field
      isAuthor : NodeId -> Maybe Author
      pkAuthor : Author -> PK
      pkInj    : ∀ (a₁ a₂ : Author)  -- Authors must have distinct public keys, otherwise a
                                     -- dishonest author can potentially impersonate an honest
                                     -- author.
               → pkAuthor a₁ ≡ pkAuthor a₂
               → a₁ ≡ a₂

    -- AuthorId : Author -> NodeId
    -- AuthorDisj : ...
  open EpochConfig public

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

  fakeAuthorsN : ℕ
  fakeAuthorsN = 4

  fakeAuthors : NodeId → Maybe (Fin fakeAuthorsN)
  fakeAuthors nid with nid <? fakeAuthorsN
  ...| yes xx = just (fromℕ≤ xx)
  ...| no  _  = nothing

  postulate
    fakePKs    : Fin fakeAuthorsN → PK
    fakePKsInj : (x x₁ : Fin 4) (x₂ : fakePKs x ≡ fakePKs x₁) → x ≡ x₁

  fakeEC : EpochId → EpochConfig
  fakeEC eid = record {
                 epochId        = eid
               ; authorsN       = fakeAuthorsN
               ; bizF           = 1
               ; isBFT          = s≤s (s≤s (s≤s (s≤s z≤n)))
               ; seed           = 0
               ; ecInitialState = dummyHash
               ; isAuthor       = fakeAuthors
               ; pkAuthor       = fakePKs
               ; pkInj          = fakePKsInj
               }

  -- Records parameterized by a type of author execpt the initial
  -- record.
  --
  -- The initial record is unique per epoch. Essentially, we just
  -- use the 'epochSeed' and the hash of the last record of the previous
  -- epoch to piggyback the initial record.
  data Initial : Set where
    mkInitial : Initial

  -- All the other records will draw their authors from
  -- a given Set. They are named with a 'B' prefix standing for
  -- 'Basic' records.
  module _ (author : Set) where
   record BBlock  : Set where
     constructor mkBlock
     field
       bEpochId    : EpochId
       bAuthor     : author
       bCommand    : Command
       bPrevQCHash : QCHash
       bRound      : Round
   open BBlock public

   record BVote  : Set where
     constructor mkVote
     field
       vEpochId   : EpochId
       vAuthor    : author
       vBlockHash : BlockHash
       vRound     : Round
       vOrder     : VoteOrder 
       --vState     : State
   open BVote public

   record BQC (votes : Set) : Set where
    field
      qEpochId       : EpochId
      qAuthor        : author
      qBlockHash     : BlockHash
      qRound         : Round
      qVotes         : List votes
      --qState         : State
   open BQC public

   record BTimeout : Set where
     constructor mkTimeout
     field
       toAuthor  : author
       toRound   : Round
   open BTimeout public

   -- This is a notification of a commit.  It will probably have something different in it.
   record BC : Set where
     constructor mkCommitMsg
     field
       cEpochId : EpochId
       cAuthor  : author
       cRound   : Round
       cCert    : QCHash
   open BC public

  BVote-map : ∀{A B} → (A → B) → BVote A → BVote B
  BVote-map f bv = record 
   { vEpochId   = vEpochId bv 
   ; vAuthor    = f (vAuthor bv) 
   ; vBlockHash = vBlockHash bv  
   ; vRound     = vRound bv
   ; vOrder     = vOrder bv
   }

  postulate
   instance
     encBBlock  : ∀{A}⦃ encA : Encoder A ⦄ → Encoder (BBlock A)
     encBVote   : ∀{A}⦃ encA : Encoder A ⦄ → Encoder (BVote  A)
     encBQC     : ∀{A V}⦃ encA : Encoder A ⦄ ⦃ encV : Encoder V ⦄ 
                → Encoder (BQC A V)
     encBC      : ∀{A}⦃ encA : Encoder A ⦄ → Encoder (BC A)

