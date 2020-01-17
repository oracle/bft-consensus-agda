{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.Encode
open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.EventProcessor
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec      : EpochConfig)
   where

 open import LibraBFT.Concrete.BlockTree hash hash-cr

 record EventProcessor : Set where
   constructor nodeState
   field
     myPK           : PK -- TODO: this is temporary until we have a better model
     -- TODO: for now, we omit the levels of indirection between BlockStore and BlockTree
     epBlockStore   : BlockTree ec
 open EventProcessor public

 -- VCM: PROPOSAL TO HANDLE PRIV KEYS
 --
 -- Let mkSigned be a postulate; and ensure that
 -- whenever we sign a message with a nodeState 
 -- it can only be checked by this node's public key
 --
 -- Curiously; this drops the need for our IsKeyPair predicate
 -- Nevertheless, I'd advocate not making any decisions until
 -- its time we come to need these.
 postulate 
   mkSigned : {A : Set} ⦃ encA : Encoder A ⦄ 
            → EventProcessor → A → Signed A

   mkSigned-correct-1 
     : ∀{A}⦃ encA : Encoder A ⦄
     → (st : EventProcessor)(x : A)
     → verify (encode x) 
              (signature (mkSigned st x)) 
              (myPK st)
       ≡ true

   mkSigned-correct-2
     : ∀{A}⦃ encA : Encoder A ⦄
     → (st : EventProcessor)(x : A)(pk : PK)
     → verify (encode x) 
              (signature (mkSigned st x)) 
              pk
        ≡ true
     → pk ≡ (myPK st)
