open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.EpochConfig
open import LibraBFT.Concrete.Util.HashMap

open import Relation.Unary hiding (_∈_)
open import Data.List.Relation.Unary.Any

{- VCM: THIS DESIGN IS NOT FINAL; check comments on InsertValidRecord -}
module LibraBFT.Concrete.RecordStoreState.ValidateNetworkRecord
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Concrete.RecordStoreState hash hash-cr
  open RecordStoreStateMut
  import      LibraBFT.Abstract.Records as Abstract

  -- VCM TODO
  -- A valid record should be with respect to the 
  -- immutable part of the concrete RSS
  ValidRecord : RecordStoreState → Set₁
  ValidRecord rss = Abstract.Record (ecAbstract (rssConfig rss))


  postulate ForMark : ∀{a}{A : Set a} → A

  validateBlockQCHash : (rss : RecordStoreState)
                      → QCHash
                      → Maybe (ValidRecord rss)

  -- Here's the function that is supposed to validate network records
  -- for a given record store state.
  validateNetworkRecord : (rss : RecordStoreState)
                        → Record
                        → Maybe (ValidRecord rss)
  validateNetworkRecord rss (Q q) = ForMark
  validateNetworkRecord rss (B (signed blk author sig))

     -- MSM How do we know we did the verification?  What if I just make
     -- something up here, for a record that doesn't verify?  What will go
     -- wrong?

     -- Check if author is active in epoch
     with Data.List.Relation.Unary.Any.any (_≟ author blk)
                                           (ecValidAuthors (rssConfig rss))
  ...| no   _ = nothing
  ...| yes authIdx

       -- TODO: Check if sig verifies (do we have anything modeled for this yet?)

         -- Check that bPrevQCHash refers to previously verified record
         with (rssQCs ∘ rssMutablePart) rss (bPrevQCHash blk)
  ...|     nothing = nothing  -- MSM: But what if previous is Initial?
  ...|     just qc

           -- Check round monotonicity
           with qRound qc <? bRound blk
  ...|       no  _  = nothing
  ...|       yes ok = -- MSM: Where will the ok check be used?
                      just (Abstract.B (mkBlock
                                         (index authIdx)
                                         (bCommand    blk)
                                         (bPrevQCHash blk)
                                         (bRound      blk)))

