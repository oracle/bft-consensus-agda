open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.EpochConfig
open import LibraBFT.Concrete.Util.HashMap

{- VCM: THIS DESIGN IS NOT FINAL; check comments on InsertValidRecord -}
module LibraBFT.Concrete.RecordStoreState.ValidateNetworkRecord
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Concrete.RecordStoreState hash hash-cr
  import      LibraBFT.Abstract.Records as Abstract

  -- VCM TODO
  -- A valid record should be with respect to the 
  -- immutable part of the concrete RSS
  ValidRecord : RecordStoreState → Set₁
  ValidRecord rss = Abstract.Record (ecAbstract (rssConfig rss))


  postulate ForMark : ∀{a}{A : Set a} → A

  -- Here's the function that is supposed to validate network records
  -- for a given record store state.
  validateNetworkRecord : (rss : RecordStoreState)
                        → Record
                        → Maybe (ValidRecord rss)
  validateNetworkRecord rss (Q q) = ForMark
  validateNetworkRecord rss (B (signed blk author sig)) =
     -- Check if (author blk) is in (ecValidAuthors (rssConfig rss)), determine author index
     -- Check if sig verifies (do we have anything modeled for this yet?)
     -- But how do we know we did the verification?  What if I just make something up here,
     -- for a record that doesn't verify?  What will go wrong?

     -- For now, no verification is done at all.
     just (Abstract.B (mkBlock {! author index determined above!}
                               (bCommand    blk)
                               (bPrevQCHash blk)
                               (bRound      blk)))

  

