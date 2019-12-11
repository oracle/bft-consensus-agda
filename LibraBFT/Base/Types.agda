open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS

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

    -- AuthorId : Author -> NodeId
    -- AuthorDisj : ...
  open EpochConfig public

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
       bAuthor     : author
       bCommand    : Command
       bPrevQCHash : QCHash
       bRound      : Round
   open BBlock public

   record BVote  : Set where
     constructor mkVote
     field
       vAuthor    : author
       vBlockHash : BlockHash
       vRound     : Round
       vOrder     : VoteOrder 
       --vState     : State
   open BVote public

   record BQC (votes : Set) : Set where
    field
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
