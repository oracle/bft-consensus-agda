open import Hash
open import BasicTypes
open import Prelude

module RecordChain {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open WithCryptoHash hash hash-cr
  open import Records ec
  -- Hash Functions ----------------------------------------------
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR : Record → Hash
  HashR = hash ∘ encodeR


  data _←_ : Record → Record → Set where
    I←B : ∀ {a} {i : Initial} {b : Block a}
          → HashR (I i) ≡  bPrevQCHash b
          → I i ← B b
    Q←B : ∀ {a a'} {q : QC a} {b : Block a'}
          → HashR (Q q) ≡  bPrevQCHash b
          → Q q ← B b
    B←Q : ∀ {a a'} {b : Block a} {q : QC a'}
          → HashR (B b) ≡ qBlockHash q
          → B b ← Q q
    B←V : ∀ {a a'} {b : Block a} {v : Vote a'}
          → HashR (B b) ≡ vBlockHash v
          → B b ← V v

  data _←⋆_ (r₁ : Record) (r₂ : Record) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂
