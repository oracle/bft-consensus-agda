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


  mutual
  
    data Valid : ∀ {r} → RecordChain r → Record → Set where
      ValidBlockInit : ∀ {a} {b : Block a} → 1 ≤ bRound b → Valid empty (B b)
      ValidBlockStep : ∀ {a a'} {b : Block a} {q : QC a'}
                     → ( rc : RecordChain (Q q) )
                     →  qRound q < bRound b
                     → Valid rc (B b)
      -- It's the leader that proposes the Block that sends the QC therefore we enforce it
      -- by asking just one author
      ValidQC        : ∀ {a} {q : QC a} {b : Block a}
                     → (rc : RecordChain (B b))
                     → qRound q ≡ bRound b
                     → Valid rc (Q q)

    data RecordChain : Record → Set where
      empty : ∀ {hᵢ} → RecordChain (I hᵢ)
      step  : ∀ {r r'} → (rc : RecordChain r) → r ← r' → Valid rc r' → RecordChain r'

