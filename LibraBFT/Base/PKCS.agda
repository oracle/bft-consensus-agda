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

  verify-sign : ∀{bs pk sk}
              → IsKeyPair pk sk
              → verify bs (sign bs sk) pk ≡ true

 record Signed (A : Set) ⦃ encA : Encoder A ⦄ : Set where
   constructor signed
   field
     content   : A
     signature : Signature
 open Signed public

 record VerSigned (A : Set) ⦃ encA : Encoder A ⦄ : Set where
   constructor ver-signed
   field
     content   : A
     signature : Signature 
     verified  : ∃[ pk ] (verify (encode content) signature pk ≡ true)
 open VerSigned public

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

