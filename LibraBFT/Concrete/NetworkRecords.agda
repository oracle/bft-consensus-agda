{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Records

-- VCM: I've added EpochId fields to all records directly;
-- this enables us to do a single verification step
-- and ensures the datatypes are homogeneous througout the code.


module LibraBFT.Concrete.NetworkRecords where

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecord : Set where
    B : Signed (BBlock NodeId)                      → NetworkRecord
    V : Signed (BVote NodeId)                       → NetworkRecord
    Q : Signed (BQC NodeId (Signed (BVote NodeId))) → NetworkRecord
    C : Signed (BC NodeId)                          → NetworkRecord
    --- ... TOFINISH


