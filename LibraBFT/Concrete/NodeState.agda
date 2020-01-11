{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.Encode
open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.NodeState
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 open import LibraBFT.Concrete.RecordStoreState hash hash-cr

 record NodeState : Set where
   constructor nodeState
   field
     myPK           : PK
     lastVotedRound : Round
 open NodeState public

 postulate
   abstractEpochConfig : NodeState → EpochConfig  -- TODO: EpochConfig is an Abstract concept, we will need to
                                                  -- construct it from the concrete NodeState

 record NodeStateWithProps : Set where
   field
     state  : NodeState
     auxRSS : RecordStoreState (abstractEpochConfig state)


 leader? : NodeState → Bool
 leader? = {!!}

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
            → NodeState → A → Signed A

   mkSigned-correct-1 
     : ∀{A}⦃ encA : Encoder A ⦄
     → (st : NodeState)(x : A)
     → verify (encode x) 
              (signature (mkSigned st x)) 
              (myPK st)
       ≡ true

   mkSigned-correct-2
     : ∀{A}⦃ encA : Encoder A ⦄
     → (st : NodeState)(x : A)(pk : PK)
     → verify (encode x) 
              (signature (mkSigned st x)) 
              pk
        ≡ true
     → pk ≡ (myPK st)
