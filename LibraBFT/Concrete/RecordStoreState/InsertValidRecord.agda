open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.EpochConfig
open import LibraBFT.Concrete.Util.HashMap


module LibraBFT.Concrete.RecordStoreState.InsertValidRecord 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Concrete.RecordStoreState                       hash hash-cr
  open import LibraBFT.Concrete.RecordStoreState.ValidateNetworkRecord hash hash-cr

  import LibraBFT.Abstract.Records as Abstract

  -- One option, is to say that we only insert valid records and split the validation
  -- into another file; as we have right now.
  --
  -- Another option, which might be closer to our Haskell implementation,
  -- would be to have 'insertNetworkRecord : RecordStoreState → Concrete.Record → Maybe RecordStoreState'
  --  
  -- I'm unsure of which one I actually prefer. This is just a sketch for now anyway
  insertValidRecord : (rss : RecordStoreState) → ValidRecord rss → RecordStoreState
  insertValidRecord = {!!}
 
  -- Now we can prove invariants about the insertValidRecord function

  insert-isValid : (rss : RecordStoreState)(r : ValidRecord rss)
                 → ValidRSS rss
                 → ValidRSS (insertValidRecord rss r)
  insert-isValid = {!!}


  insert-incr-round-ok : (rss : RecordStoreState)(r : ValidRecord rss)
                       → NoIncreasingRoundBroke rss
                       → NoIncreasingRoundBroke (insertValidRecord rss r)
  insert-incr-round-ok = {!!}

  -- etc
