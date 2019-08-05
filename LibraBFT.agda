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


  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  _←_ : Hash → Record → Set
  h ← block b = h ≡ Block.prevQCHash b
  h ← qc    q = h ≡ QC.blockHash q

  -- Definition of R₁ ←⋆ R₂
  -- Termination check problem

  {-# TERMINATING #-}
  _←⋆_ : Hash → Record → Set
  h ←⋆ r = (h ← r) ⊎ (∃[ r₁ ] (h ←⋆ r₁ × (hashR r₁) ← r))

  {-
  _←⋆_ : {hᵢ : HInit} {rec : Record} {rs : RecordStore hᵢ}
         → Hash → Valid rec rs → Set
  _←⋆_ {hᵢ} {block b} {empty} h r = hᵢ ≡ Block.prevQCHash b
  _←⋆_ {hᵢ} {block b} {insert rs r v} h ⟨ q , ⟨ vQ , ⟨ q←b  , snd ⟩ ⟩ ⟩
    =   {!!} × {!!} --∃[ r₁ ] ((hashR r₁) ← (qc q) × h ←⋆ v)
  _←⋆_ {hᵢ} {qc x₁} {insert rs r₁ x} h r = {!!}
  -}

  -- Lemma S₁ ---------------------------------------------------

  hᵢ←⋆R : ∀ {hᵢ : HInit} {r : Record} {rs : RecordStore hᵢ}
            (v : Valid r rs)
          → hᵢ ←⋆ r
  hᵢ←⋆R {hᵢ} {block b} {empty}         hᵢ≡hb = inj₁ hᵢ≡hb
  hᵢ←⋆R {hᵢ} {block b} {insert rs r p} ⟨ q , ⟨ vQ , ⟨ hq≡hb , snd ⟩ ⟩ ⟩
      = inj₂ ⟨ (qc q) , ⟨ hᵢ←⋆R vQ , hq≡hb ⟩ ⟩
  hᵢ←⋆R {hᵢ} {qc x}    {insert rs r x₁} ⟨ b , ⟨ vB , ⟨ hb≡hq , snd ⟩ ⟩ ⟩
      = inj₂ ⟨ (block b) , ⟨ (hᵢ←⋆R vB) , hb≡hq ⟩ ⟩


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
  round-mono vr₀ vr₁ vr₂ ⟨ inj₁ r₀←b₂ , inj₁ b₁←b₂ ⟩ rr₀<rr = {!!}
  --  with (←inj r₀←b₂ b₁←b₂)
  --...| x = ?
  round-mono {r₁ = block b₁} {block b₂} vr₀ vr₁ vr₂ ⟨ inj₂ y , inj₁ h←r ⟩ rr₀<rr = {!!}
  round-mono {r₁ = qc x} {block b} vr₀ vr₁ vr₂ ⟨ r₀←⋆r₂ , inj₁ h←r ⟩ rr₀<rr = {!!}
  round-mono {r₂ = qc x} vr₀ vr₁ vr₂ ⟨ r₀←⋆r₂ , inj₁ h←r ⟩ rr₀<rr = {!!}
  round-mono vr₀ vr₁ vr₂ ⟨ r₀←⋆r₂ , inj₂ y ⟩ rr₀<rr = {!!}

  {-
  round-mono vr₀ vr₁ vr₂ (inj₁ r₀←r₂) (inj₁ r₁←r₂) rr₀<r = ?
  --  with (←inj r₀←r₂ r₁←r₂)
  --...| inj₁ x = {!!}
  ...| inj₂ y = ?
  round-mono vr₀ vr₁ vr₂ (inj₁ x) (inj₂ y) rr₀<r = {!!}
  round-mono vr₀ vr₁ vr₂ (inj₂ y) (r₁←r₂) rr₀<r = {!!}
  -}
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
