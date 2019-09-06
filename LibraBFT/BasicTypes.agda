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

