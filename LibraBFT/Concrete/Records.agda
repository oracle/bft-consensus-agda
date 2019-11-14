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
  record Signed (A : Set) : Set where
    constructor signed
    field
      sContent    : A
      sAuthor     : A → NodeId
      sSignature  : Signature
  open Signed public

  Block : Set
  Block = Signed (BBlock NodeId)

  QC : Set
  QC = Signed (BQC NodeId)

  Vote : Set
  Vote = Signed (BVote NodeId)

  Timeout : Set
  Timeout = Signed (BTimeout NodeId) 

  data Record : Set where
    B : Block     → Record
    Q : QC        → Record
    -- V : Vote      → Record
    -- T : Timeout   → Record


