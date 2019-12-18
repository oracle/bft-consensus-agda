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

  sign   : ByteString → SK → Signature
  verify : ByteString → Signature → PK → Bool

  -- MSM: this doesn't preclude an implementation in which verify always returns true.  Should we
  -- assume no "signature collisions", and also postulate that a signature does NOT verify if not
  -- constructed with a key pair (I added it below)?  I don't fully understand how these will be
  -- used, so I am not sure, but hopefully my comments and questions help to elucidate this.
  verify-sign : ∀{bs pk sk}
              → IsKeyPair pk sk
              → verify bs (sign bs sk) pk ≡ true

  verify-fail : ∀{bs pk sk}
              → ¬ IsKeyPair pk sk
              → verify bs (sign bs sk) pk ≡ false

 record Signed (A : Set) ⦃ encA : Encoder A ⦄ : Set where
   constructor signed
   field
     content   : A
     signature : Signature
 open Signed public

 -- MSM: This doesn't make intuitive sense to me as changing the content (by mapping f over it)
 -- would also change the signature, which this doesn't.  I see that the only place where this is
 -- used (RecordStoreState.Agda) will actually map an author (index) into the relevant NodeId, which
 -- would be what was used to construct the original signature, so I guess it makes sense, but I
 -- think we should have some comment explaining this (perhaps based on this comment, but I want to
 -- check my understanding first).
 Signed-map : ∀{A B} ⦃ encA : Encoder A ⦄ ⦃ encB : Encoder B ⦄
            → (A → B) → Signed A → Signed B
 Signed-map f s = signed (f (content s)) (signature s)

 record VerSigned (A : Set) ⦃ encA : Encoder A ⦄ : Set where
   constructor ver-signed
   field
     content   : A
     signature : Signature
     pk        : PK
     verified  : verify (encode content) signature pk ≡ true
 open VerSigned public

 checkSignature : ∀{A} ⦃ encA : Encoder A ⦄ 
                → (pk : PK) → (sa : Signed A)
                → Maybe (Σ (VerSigned A) (λ vs → VerSigned.pk vs ≡ pk
                                               × VerSigned.content vs ≡ Signed.content sa))
 checkSignature pk obj 
   with verify (encode (content obj)) (signature obj) pk
      | inspect (verify (encode (content obj)) (signature obj)) pk 
 ...| false | _     = nothing 
 ...| true  | [ R ] = just (ver-signed (content obj) (signature obj) pk R , (refl , refl))

 instance 
  encSigned : {A : Set} → ⦃ encA : Encoder A ⦄ → Encoder (Signed A)
  encSigned = record 
    { encode     = λ s → proj₁ (signature s) ++ encode (content s) 
    ; encode-inj = todo
    } where postulate todo : ∀{a}{A : Set a} → A

  encVerSigned : {A : Set} → ⦃ encA : Encoder A ⦄ → Encoder (VerSigned A)
  encVerSigned = record 
    { encode     = λ s → proj₁ (signature s) ++ encode (content s) 
    ; encode-inj = todo
    } where postulate todo : ∀{a}{A : Set a} → A

