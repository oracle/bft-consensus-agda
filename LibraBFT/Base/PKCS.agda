open import LibraBFT.Prelude
open import LibraBFT.Base.Encode


module LibraBFT.Base.PKCS where

 postulate 
   signature-size : ℕ

 Signature : Set
 Signature = Σ ByteString (λ s → length s ≡ signature-size)

 postulate
  PK : Set
  SK : Set
  IsKeyPair : PK → SK → Set

  sign-raw : ByteString → SK → Signature
  verify   : ByteString → Signature → PK → Bool

  -- MSM: this doesn't preclude an implementation in which verify always returns true.  Should we
  -- assume no "signature collisions", and also postulate that a signature does NOT verify if not
  -- constructed with a key pair (I added it below)?  I don't fully understand how these will be
  -- used, so I am not sure, but hopefully my comments and questions help to elucidate this.
  verify-sign : ∀{bs pk sk}
              → IsKeyPair pk sk
              → verify bs (sign-raw bs sk) pk ≡ true

  verify-fail : ∀{bs pk sk}
              → ¬ IsKeyPair pk sk
              → verify bs (sign-raw bs sk) pk ≡ false

 -- A datatype C might that might carry values with
 -- signatures should be an instance of 'WithSig' below.
 record WithSig (C : Set) : Set₁ where
   field
     -- A decidable predicate indicates whether values have
     -- been signed 
     Signed         : C → Set
     isSigned?      : (c : C) → Dec (Signed c)
   
     -- Signed values must have a signature
     signature      : (c : C)(hasSig : Signed c) → Signature

     -- All values must be /encoded/ into a ByteString that
     -- is supposed to be verified against a signature.
     signableFields : C → ByteString
 open WithSig {{...}} public

 sign : {C : Set} ⦃ ws : WithSig C ⦄ → C → SK → Signature
 sign c = sign-raw (signableFields c) 

 -- A value of a datatype C can have its signature
 -- verified; A value of type WithVerSig c is a proof of that.
 -- Hence; the set (Σ C WithVerSig) is the set of values of
 -- type C with verified signatures.
 record WithVerSig {C : Set} ⦃ ws : WithSig C ⦄ (c : C) : Set where
   field
     isSigned  : Signed c
     verWithPK : PK
     verified  : verify (signableFields c) (signature c isSigned) verWithPK
               ≡ true
 open WithVerSig public
 
 check-signature : {C : Set} ⦃ ws : WithSig C ⦄ → PK → (c : C) → Maybe (WithVerSig c)
 check-signature pk c with isSigned? c
 ...| no  _  = nothing
 ...| yes sc with verify (signableFields c) (signature c sc) pk
                | inspect (verify (signableFields c) (signature c sc)) pk
 ...| false |   _   = nothing
 ...| true  | [ R ] = just (record { isSigned  = sc 
                                   ; verWithPK = pk 
                                   ; verified  = R })
