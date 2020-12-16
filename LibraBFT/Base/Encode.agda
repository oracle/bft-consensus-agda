{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Base.ByteString

module LibraBFT.Base.Encode where

 -- An encoder for values of type A is
 -- an injective mapping of 'A's into 'ByteString's
 record Encoder {a}(A : Set a) : Set a where
   field
     encode     : A → ByteString
     encode-inj : ∀{a₁ a₂} → encode a₁ ≡ encode a₂ → a₁ ≡ a₂
 open Encoder {{...}} public

 postulate  -- valid assumption
  instance
    encℕ   : Encoder ℕ
    encBS  : Encoder ByteString

 instance
   encFin : {n : ℕ} → Encoder (Fin n)
   encFin {n} = record { encode     = encode ⦃ encℕ ⦄ ∘ toℕ ;
                         encode-inj = toℕ-injective ∘ encode-inj ⦃ encℕ ⦄ }
