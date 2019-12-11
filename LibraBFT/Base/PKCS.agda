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

 Signed-map : ∀{A B} ⦃ encA : Encoder A ⦄ ⦃ encB : Encoder B ⦄
            → (A → B) → Signed A → Signed B
 Signed-map f s = signed (f (content s)) (signature s)

 record VerSigned (A : Set) ⦃ encA : Encoder A ⦄ : Set where
   constructor ver-signed
   field
     content   : A
     signature : Signature 
     verified  : ∃[ pk ] (verify (encode content) signature pk ≡ true)
 open VerSigned public

 checkSignature : ∀{A} ⦃ encA : Encoder A ⦄ 
                → PK → Signed A → Maybe (VerSigned A)
 checkSignature pk obj 
   with verify (encode (content obj)) (signature obj) pk
      | inspect (verify (encode (content obj)) (signature obj)) pk 
 ...| false | _     = nothing 
 ...| true  | [ R ] = just (ver-signed (content obj) (signature obj) (pk , R))

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

