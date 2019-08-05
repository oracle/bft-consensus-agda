open import Data.Nat
open import Data.List renaming (map to List-map)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.List.Any
open import Data.List.All
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)


open import Hash

module LibraBFT
  -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open WithCryptoHash hash hash-cr

 ------------------------- AuxTypes ----------------------------
  record Author : Set where
    field
      id : ℕ
      privKey : ByteString

  -- I think it also needs the leader
  EpochId : Set
  EpochId = ℕ

  Round : Set
  Round = ℕ

  Command : Set
  Command = ℕ

  -- Can be a function that receives the QC and return a hash
  QCHash : Set
  QCHash = Hash

  BlockHash : Set
  BlockHash = Hash

  -- don't know if it's better to model the threshold-signature
  Signature : Set
  Signature = Hash

  HInit : Set
  HInit = QCHash

  State : Set
  State = Hash

 ----------------------------------------------------------------


 --------------------------- Record -----------------------------

 -- Block ------------------------------------------
 -- Don't know if it needs the epoch or the round
  record Block : Set where
    field
      --command    : Command
      prevQCHash : QCHash
      round      : Round
      author     : Author
      --signature  : Signature

 -- Vote -------------------------------------------
  record Vote : Set where
    field
      -- epoch     : EpochId
      blockHash : BlockHash
      -- state     : State
      author    : Author
      --signature : Signature

 -- QuorumCertificate ------------------------------
  record QC : Set where
    field
      -- epoch     : EpochId
      blockHash : BlockHash
      round     : Round
      -- state     : State
      votes     : List Vote
      author    : Author

  data Record : Set where
    block : Block   → Record
    qc    : QC      → Record
    -- vote    : Vote    → Record
    -- timeout : Timeout → Record

  round : Record → Round
  round (block b) = Block.round b
  round (qc q)    = QC.round q

 -- Hash Functions ---------------------------------
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  hashR = hash ∘ encodeR

  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  _←_ : Hash → Record → Set
  h ← block b = h ≡ Block.prevQCHash b
  h ← qc    q = h ≡ QC.blockHash q

  -- Definition of R₁ ←⋆ R₂
  -- Termination check problem

  data _←⋆_ (h : Hash) (r : Record) : Set where
    h←   : (h ← r) → h ←⋆ r
    _←₊_ : {rₓ : Record} → (h ←⋆ rₓ) → (hashR rₓ ← r) → h ←⋆ r


----------------------------------------------------------------


------------------------- RecordStore --------------------------

  {- 4.2 Verification of Network Records
   - The RecordStore represents the set of all records validated so far
     in a given epoch
   - Does not include constraints : 1, 5, 6, 7 and 8
   -}
  data RecordStore (h : HInit) :  Set

  Valid : {h : HInit} → Record → RecordStore h → Set

  data RecordStore h where
    empty  : RecordStore h
    insert : (s : RecordStore h) (r : Record)
            → Valid r s → RecordStore h

  {- For now I am not including in the validation the Hash of the states
   - No constraint about no dup qc elements
   -}
  Valid {h} (block b) empty           = h ≡ Block.prevQCHash b
  Valid {h} (block b) (insert rs r x) =
    ∃[ q ] ( Valid (qc q) rs
           × (hashR (qc q) ≡ Block.prevQCHash b)
           × ∃[ prevB ] ( Valid (block prevB) rs
                        × QC.blockHash q ≡ hashR (block prevB)
                        × Block.round prevB < Block.round b) )

  Valid (qc q) empty                  = ⊥
  Valid (qc q) (insert rs r x)        =
    ∃[ b ] ( Valid (block b) rs
           × hashR (block b) ≡ QC.blockHash q
           × QC.round q ≡ Block.round b
           × All (_≡_ (hashR (block b)))
                  (List-map (Vote.blockHash) (QC.votes q)) )

  -- Lemma S₁ ---------------------------------------------------

  hᵢ←⋆R : ∀ {hᵢ : HInit} {r : Record} {rs : RecordStore hᵢ}
            (v : Valid r rs)
          → hᵢ ←⋆ r
  hᵢ←⋆R {hᵢ} {block b} {empty}         hᵢ≡hb = h← hᵢ≡hb
  hᵢ←⋆R {hᵢ} {block b} {insert rs r p} v
    with v
  ... | ⟨ q , ⟨ vQ , ⟨ hq≡hb , snd ⟩ ⟩ ⟩ = hᵢ←⋆R {rs = rs} vQ ←₊ hq≡hb
  hᵢ←⋆R {hᵢ} {qc x}    {insert rs r x₁} v
    with v
  ... | ⟨ b , ⟨ vB , ⟨ hq≡hb , snd ⟩ ⟩ ⟩ = hᵢ←⋆R {rs = rs} vB ←₊ hq≡hb


  ←inj : ∀ {r₀ r₁ r₂ : Record} → (hashR r₀ ← r₂) → (hashR r₁ ← r₂)
           → r₀ ≡ r₁ ⊎ HashBroke
  ←inj {r₀} {r₁} {block b} hr₀≡phb hr₁≡phb
    with hash-cr (trans hr₀≡phb (sym hr₁≡phb))
  ... | inj₁ ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ =
             inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ ⟩
  ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)

  ←inj {r₀} {r₁} {qc q}    hr₀≡phb hr₁≡phb
    with hash-cr (trans hr₀≡phb (sym hr₁≡phb))
  ... | inj₁ ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ =
             inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ ⟩
  ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)




  round-mono : ∀  {hᵢ : HInit} {r₀ r₁ r₂ : Record} {rs : RecordStore hᵢ}
                 → Valid r₀ rs → Valid r₁ rs → Valid r₂ rs
                 → hashR r₀ ←⋆ r₂ × hashR r₁ ←⋆ r₂
                 → round r₀ < round r₁
                 → (hashR r₀ ←⋆ r₁) ⊎ HashBroke
  round-mono = {!!}

----------------------------------------------------------------


------------------------ RecordStoreState ----------------------

  record RecordStoreState : Set where
    field
      epoch     : EpochId
      hᵢ        : HInit
      recStore  : RecordStore hᵢ
      curRound  : Round
      highQCR   : Round
      listVotes : List Vote
      -- initialState : State
      -- highCommR    : Round
----------------------------------------------------------------


-------------------------- NodeState ---------------------------

  record NodeState : Set where
    field
      author    : Author
      epoch     : EpochId
      recStore  : RecordStoreState
      lockRound : Round
      -- latestVotedRound : Round
