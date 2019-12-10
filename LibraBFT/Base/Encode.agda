open import LibraBFT.Prelude

module LibraBFT.Base.Encode where

 -- An encoder for values of type A is
 -- an injective mapping of 'A's into 'ByteString's
 record Encoder {a}(A : Set a) : Set a where
   field
     encode     : A → ByteString
     encode-inj : ∀{a₁ a₂} → encode a₁ ≡ encode a₂ → a₁ ≡ a₂
 open Encoder {{...}} public
 
 postulate instance
   
