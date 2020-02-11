{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.EventProcessor
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (pki     : PKI)
  (cmd     : Set) -- VCM: review this
   where

 postulate
   initEventProcessor : {a : Set} → PK → EventProcessor a
