{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Records

module LibraBFT.Concrete.NetworkRecords where

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecordPayload {A : Set} ⦃ encA : Encoder A ⦄ : Set where
    B : (BBlock A)                 → NetworkRecordPayload
    V : (BVote A)                  → NetworkRecordPayload
    Q : (BQC A (Signed (BVote A))) → NetworkRecordPayload
 -- Commit messages to be added later
 -- C : (BC A)                     → NetworkRecordPayload

  instance
   encNWRecordPayload : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (NetworkRecordPayload {A})
   encNWRecordPayload = record
     { encode     = enc1
     ; encode-inj = λ {r} {s} → enc1-inj r s
     } where
       enc1 : NetworkRecordPayload → ByteString
       enc1 (B x) = true  ∷ false ∷ encode x
       enc1 (Q x) = false ∷ true  ∷ encode x
       enc1 (V x) = false ∷ false ∷ encode x
       -- enc1 (C x) = true  ∷ true  ∷ encode (content x)

       postulate magic : ∀{a}{A : Set a} → A

       -- TODO: Implement this later; The important bit
       --       is that Agda easily understands that the type tags
       --       work and discharges the difficult cases. 
       --       Although long; the proof for QC will be boring; I already
       --       proved the bits and pieces proof irrelevant in Lemmas.
       enc1-inj : ∀ r s → enc1 r ≡ enc1 s → r ≡ s
       enc1-inj (B x) (B x₁) hyp = magic
       enc1-inj (Q x) (Q x₁) hyp = magic
       -- enc1-inj (C x) (C x₁) hyp = magic
       enc1-inj (V x) (V x₁) hyp = magic
       -- Agda infers we can't have equal records of different types, so no need to spell out all
       -- (im)possible combinations

  record NetworkRecordBody {A : Set} ⦃ encA : Encoder A ⦄ : Set where
    constructor ntwkRecBody
    field
      epochId : EpochId
      content : NetworkRecordPayload {A}

  instance
   encNWRecordBody : {A : Set} ⦃ encA : Encoder A ⦄ → Encoder (NetworkRecordBody {A})
   encNWRecordBody = record
     { encode     = enc1
     ; encode-inj = λ {r} {s} → enc1-inj r s
     } where
       postulate magic : ∀{a}{A : Set a} → A

       enc1 : NetworkRecordBody → ByteString
       enc1 (ntwkRecBody eId content) = encode eId ++ encode content
       enc1-inj : ∀ r s → enc1 r ≡ enc1 s → r ≡ s
       enc1-inj = magic

  NetworkRecord : ∀ {A : Set} ⦃ encA : Encoder A ⦄ → Set
  NetworkRecord {A} = Signed (NetworkRecordBody {A})

