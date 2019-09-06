open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.EpochConfig
open import LibraBFT.Concrete.Util.HashMap

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

  -- Here's the function that is supposed to validate network records
  -- for a given record store state.
  validateNetworkRecord : (rss : RecordStoreState) → Record
                        → Maybe (ValidRecord rss)
  validateNetworkRecord = ForMark 
    where postulate ForMark : ∀{a}{A : Set a} → A
  

