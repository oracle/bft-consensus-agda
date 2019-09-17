open import LibraBFT.Prelude
open import LibraBFT.Hash

-- Exposition of the ground types that we build our abstract reasoning
-- over. 
module LibraBFT.BasicTypes where

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

  Signature : Set
  Signature = Hash

  State : Set
  State = Hash

  -- Records parametrized by a type of author execpt the initial
  -- record.
  --
  -- The initial record is unique per epoch. Essentially, we just
  -- use the 'epochSeed' and the hash of the last record of the previous
  -- epoch to piggyback the initial record.
  data Initial : Set where
    mkInitial : Initial

  -- All the other records will draw their autors from
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
       -- VCM: Should we keep vOrder here?
       -- The 'vOrder' is a "metafield", it keeps track of which vote from 'vAuthor'
       -- this is representing. This makes it much simpler to talk about thinks such as 
       -- the increasing round rule. 
       vOrder     : ℕ 
       --vState     : State
   open BVote public

   record BQC : Set where
    field
      qAuthor        : author
      qBlockHash     : BlockHash
      qRound         : Round
      qVotes         : List BVote
      --qState         : State
   open BQC public

   record BTimeout : Set where
     constructor mkTimeout
     field
       toAuthor  : author
       toRound   : Round
   open BTimeout public

   postulate
     -- Later on, we'll also need an 'Encoder author'...
     encBBlock   : Encoder BBlock 
     encBQC      : Encoder BQC
     encBVote    : Encoder BVote
     encBTimeout : Encoder BTimeout
