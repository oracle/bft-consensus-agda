open import Data.Nat
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.List.Any
open import Data.List.All
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction; contraposition)


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
    B  : Block   → Record
    Qc : QC      → Record
    -- vote    : Vote    → Record
    -- timeout : Timeout → Record

  round : Record → Round
  round (B b)  = Block.round b
  round (Qc q) = QC.round q

  prevHash : Record → Hash
  prevHash (B b)  = Block.prevQCHash b
  prevHash (Qc q) = QC.blockHash q

  round≢→r₀≢r₁ : ∀ {r₀ r₁ : Record} → round r₀ ≢ round r₁ → r₀ ≢ r₁
  round≢→r₀≢r₁ x refl = x refl
  -- round≢→r₀≢r₁ {Qc x₂} {Qc .x₂} x refl = {!!}

 -- Hash Functions ---------------------------------
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR = hash ∘ encodeR

  postulate
    hashR-irreflexive : ∀ {r : Record} → HashR r ≢ prevHash r


  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  data _←_ : Record → Record → Set where
    q←b : ∀ {q : QC} {b : Block}
          → HashR (Qc q) ≡  Block.prevQCHash b
          → Qc q ← B b
    b←q : ∀ {q : QC} {b : Block}
          → HashR (B b) ≡ QC.blockHash q
          → B b ← Qc q

  data _←⋆_ (r₁ r₂ : Record) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂


----------------------------------------------------------------


------------------------- RecordStore --------------------------

  data RecordStore (qcᵢ : QC) : Set

  Valid : {qcᵢ : QC} → Record → RecordStore qcᵢ → Set

  data RecordStore qcᵢ where
    empty  : RecordStore qcᵢ
    insert : {r : Record} (s : RecordStore qcᵢ)
             → Valid r s → RecordStore qcᵢ

  data _∈Rs_ {qcᵢ} (r : Record) : RecordStore qcᵢ → Set where
    here  : ∀ (s : RecordStore qcᵢ) (v : Valid r s) → r ∈Rs (insert s v)
    there : ∀ (r' : Record) (s : RecordStore qcᵢ) (v : Valid r' s)
           → r ∈Rs s
           → r ∈Rs (insert s v)

  Valid {qᵢ} (B b) empty         = Qc qᵢ ← B b
  Valid      (B b) (insert rs v) = ∃[ q ] ( q ∈Rs rs × q ← B b × round q < round (B b) )
  Valid     (Qc q) rs    = ∃[ b ] ( b ∈Rs rs × b ← Qc q × round (Qc q) ≡ round b )



  -- Other approaches for Record Store
{-
  -- 1 - Record Store as a List of all Records and the set of Verified Records
  -- would be _∈Rs_

  Valid : QC → Record → List Record → Set
  Valid qᵢ (B b)  [] = Qc qᵢ ← B b
  Valid qᵢ (B b)  rs = ∃[ q ] ( q ∈ rs × q ← B b × round q < round (B b) )
  Valid qᵢ (Qc q) [] = ⊥
  Valid qᵢ (Qc q) rs = ∃[ b ] ( b ∈ rs × b ← Qc q × round (Qc q) ≡ round b )

  data _∈Rs_ {qᵢ} (r : Record) : List Record → Set where
    here  : ∀ (s : List Record) (v : Valid qᵢ r s)
           → r ∈Rs s
    there : ∀ (r' : Record) (s : List Record) (v : Valid qᵢ r' s)
           → _∈Rs_ {qᵢ} r s
           → r ∈Rs (r' ∷ s)
-}
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------

{-
  -- 2 - Record Store as a set where the constructores ensure that there is a previous
  -- verified record in the set. However I couldn't define the _∈Rs for this case, as
  -- this predicate and the Record Store are dependent on each other. But I will leave
  -- it here in case you want to have a look.

  round≤ : Record → Record → Set
  round≤ (B b₁) (Qc q) = Block.round b₁ ≡ QC.round q
  round≤ (Qc q) (B b)  = QC.round q < Block.round b
  round≤ _ _           = ⊥

  data RecordStore (qcᵢ : QC) : Set

  _∈Rs_ : ∀ {qcᵢ : QC} → Record → RecordStore qcᵢ → Set

  data RecordStore qcᵢ where
    empty : ∀ {b : Block}
            → Qc qcᵢ ← B b
            → RecordStore qcᵢ
    insR  : ∀ {r : Record} (new : Record) (rs : RecordStore qcᵢ)
            → r ∈Rs rs
            → r ← new
            → round≤ r new
            → RecordStore qcᵢ

  r ∈Rs rs = {!!}
-}


{-
-- Lemma S₁ ---------------------------------------------------

  hᵢ←⋆R : ∀ {hᵢ : Hash} {r : Record} {rs : RecordStore hᵢ}
            (v : Valid r rs)
          → hᵢ ←⋆ r
  hᵢ←⋆R {qᵢ} {B b}  {empty}         v = h← v
  hᵢ←⋆R {qᵢ} {B b}  {insert rs r x} v
    with v
  ... | ⟨ q , ⟨ vQ , ⟨ q←b , snd ⟩ ⟩ ⟩ = hᵢ←⋆R {rs = rs} vQ ←⁺ q←b
  hᵢ←⋆R {qᵢ} {Qc q} {insert rs r x} v
    with v
  ... | ⟨ b , ⟨ vB , ⟨ b←q , snd ⟩ ⟩ ⟩ = hᵢ←⋆R {rs = rs} vB ←⁺ b←q



  ←inj : ∀ {r₀ r₁ r₂ : Record} → (HashR r₀ ← r₂) → (HashR r₁ ← r₂)
           → r₀ ≡ r₁ ⊎ HashBroke
  ←inj {r₀} {r₁} {B b}  r₀←r₂ r₁←r₂
    with hash-cr (trans r₀←r₂ (sym r₁←r₂))
  ... | inj₁ ⟨ er₀≢er₁ , r₀←r₁ ⟩ =
             inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , r₀←r₁ ⟩ ⟩
  ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)

  ←inj {r₀} {r₁} {Qc q} r₀←r₂ r₁←r₂
    with hash-cr (trans r₀←r₂ (sym r₁←r₂))
  ... | inj₁ ⟨ er₀≢er₁ , r₀←r₁ ⟩ =
             inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , r₀←r₁ ⟩ ⟩
  ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)


  --≡⇒≤ : ∀ {m n} → m ≡ n → m ≤ n
  --≡⇒≤ {zero} {zero} x = z≤n
  --≡⇒≤ {suc m} {suc n} x = s≤s (≡⇒≤ (suc-injective x))

  r₀←⋆r₁→rr₀≤rr₁ : {hᵢ : Hash} {r₀ r₁ : Record} {rs : RecordStore hᵢ}
                 → Valid r₀ rs → Valid r₁ rs
                 → HashR r₀ ←⋆ r₁
                 → round r₀ ≤ round r₁
  r₀←⋆r₁→rr₀≤rr₁ {r₀ = B x₃} {B x₄} {empty} vr₀ vr₁ (h← x) = {!!}
  r₀←⋆r₁→rr₀≤rr₁ {r₀ = B x₃} {B x₄} {empty} vr₀ vr₁ (x₂ ←⁺ x) = {!!}
  r₀←⋆r₁→rr₀≤rr₁ {hᵢ} {r₀} {r₁} {insert rs r x₃} x x₁ x₂ = {!!}


  round-mono : ∀  {hᵢ : Hash} {r₀ r₁ r₂ : Record} {rs : RecordStore hᵢ}
                  (v₀ : Valid r₀ rs) (v₁ : Valid r₁ rs) (v₂ : Valid r₂ rs)
                 → HashR r₀ ←⋆ r₂ → HashR r₁ ←⋆ r₂
                 → round r₀ < round r₁
                 → (HashR r₀ ←⋆ r₁) ⊎ HashBroke
  round-mono {hᵢ} {r₀} {r₁} {r₂} {rs} v₀ v₁ v₂ (h← r₀←r₂) (h← r₁←r₂) rr₀<rr₁
    with ←inj r₀←r₂ r₁←r₂
  ... | inj₁ refl =  ⊥-elim (<⇒≢ rr₀<rr₁ refl)
  ... | inj₂ hashBroke = inj₂ hashBroke
  round-mono {hᵢ} {r₀} {r₁} {r₂} {rs} v₀ v₁ v₂ (h← r₀←r₂) (r₁←⋆rₓ ←⁺ rₓ←r₂) rr₀<rr₁
    with ←inj r₀←r₂ rₓ←r₂
  ... | inj₁ r₀≡rₓ =
        let r₁≤r₀ = r₀←⋆r₁→rr₀≤rr₁ v₁ v₀ (subst (HashR r₁ ←⋆_) (sym r₀≡rₓ) r₁←⋆rₓ)
        in ⊥-elim (≤⇒≯ r₁≤r₀ rr₀<rr₁)
  ... | inj₂ hashBroke = inj₂ hashBroke
  round-mono {hᵢ} {r₀} {r₁} {r₂} {rs} v₀ v₁ v₂ (r₀←⋆rₓ ←⁺ rₓ←r₂) (h← r₁←r₂) rr₀<rr
    with ←inj r₁←r₂ rₓ←r₂
  ... | inj₁ r₁≡rₓ = inj₁ (subst (HashR r₀ ←⋆_) (sym r₁≡rₓ) r₀←⋆rₓ)
  ... | inj₂ hashbroke = inj₂ hashbroke
  round-mono {hᵢ} {r₀} {r₁} {r₂} {rs} v₀ v₁ v₂ (r₀←⋆rₓ ←⁺ rₓ←r₂) (r₁←⋆rₓ₁ ←⁺ rₓ₁←r₂) rr₀<rr = {!!}

-}

----------------------------------------------------------------


------------------------ RecordStoreState ----------------------

  record RecordStoreState : Set where
    field
      epoch     : EpochId
      qᵢ        : QC
      recStore  : RecordStore qᵢ
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

