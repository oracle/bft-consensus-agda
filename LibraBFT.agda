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

  ValidBlock : {qcᵢ : QC} → Block → RecordStore qcᵢ → Set
  ValidBlock {qcᵢ} b rs =  ∃[ q ] ( q ∈Rs rs × q ← B b × round q < round (B b) )
                           ⊎
                           (Qc qcᵢ) ← (B b) × 1 ≤ round (B b)

  Valid {qcᵢ} (B b) rs = ValidBlock b rs
  Valid      (Qc q) rs = ∃[ b ] ( b ∈Rs rs × b ← Qc q × round (Qc q) ≡ round b )



-- Lemma S₁ ---------------------------------------------------

  -- 1
  hᵢ←⋆R : ∀ {qᵢ : QC} {r : Record} {s : RecordStore qᵢ}
          → r ∈Rs s
          → (Qc qᵢ) ←⋆ r
  hᵢ←⋆R {qᵢ} {B b}  {insert empty vB}    (here empty vB)
    with vB
  ... | inj₂ ⟨ qᵢ←B , 1≤rB ⟩ = ss0 qᵢ←B
  hᵢ←⋆R {qᵢ} {B b}  {insert (insert s vr) vB} (here (insert s vr) vB)
    with vB
  ... | inj₁ ⟨ q , ⟨ q∈rs , ⟨ q←B , snd ⟩ ⟩ ⟩ = let qᵢ←q = hᵢ←⋆R q∈rs
                                                 in ssr qᵢ←q q←B
  ... | inj₂ ⟨ qᵢ←B , 1≤rB ⟩                  = ss0 qᵢ←B
  hᵢ←⋆R {qᵢ} {Qc q} {insert s vQ} (here s vQ)
    with vQ
  ... |       ⟨ b , ⟨ b∈rs , ⟨ b←Q , snd ⟩ ⟩ ⟩ = let qᵢ←b = hᵢ←⋆R b∈rs
                                                 in ssr qᵢ←b b←Q
  hᵢ←⋆R {qᵢ} {r} {insert s v} (there r' s v x) = hᵢ←⋆R x


  -- 2
  ←inj : ∀ {r₀ r₁ r₂ : Record} → (r₀ ← r₂) → (r₁ ← r₂)
           → r₀ ≡ r₁ ⊎ HashBroke
  ←inj {Qc q₀} {Qc q₁} {B b} (q←b q₀←b) (q←b q₁←b)
    with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩
             = inj₂ ⟨ ⟨ (encodeR (Qc q₀) ) , (encodeR (Qc q₁) ) ⟩ , ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩ ⟩
  ... | inj₂ q₁≡q₂ = inj₁ (encodeR-inj q₁≡q₂)
  ←inj {B b₀} {B b₁} {Qc q} (b←q b₀←q) (b←q b₁←q)
    with hash-cr (trans b₀←q (sym b₁←q))
  ... | inj₁ ⟨ b₀≢b₁ , hb₀←hb₁ ⟩
             = inj₂ ⟨ ⟨ (encodeR (B b₀)) , (encodeR (B b₁)) ⟩ , ⟨ b₀≢b₁ , hb₀←hb₁ ⟩ ⟩
  ... | inj₂ b₀≡b₁ = inj₁ (encodeR-inj b₀≡b₁)


  -- 3
  ←⋆inv :  ∀ {r₀ r₁ r₂ : Record} → (r₀ ← r₁) → (r₁ ←⋆ r₂) → (r₀ ←⋆ r₂)
  ←⋆inv {r₀} {r₁} {r₂} r₀←r₁ (ss0 r₁←r₂)      = ssr (ss0 r₀←r₁) r₁←r₂
  ←⋆inv {r₀} {r₁} {r₂} r₀←r₁ (ssr r₁←⋆r r←r₂) = ssr (←⋆inv r₀←r₁ r₁←⋆r) r←r₂

  -- Aux Lemma
  ¬r←⋆r : ∀  {qᵢ : QC} {r : Record} {s : RecordStore qᵢ}
             → r ∈Rs s
             → ¬ (r ←⋆ r)
  ¬r←⋆r {qᵢ} {r} {s} r∈s (ss0 ())
  ¬r←⋆r {qᵢ} {r} {s} r∈s (ssr r←⋆r₁ r₁←r) = {!!}



  -- Aux Lemma
  ¬r←⋆qᵢ : ∀  {qᵢ : QC} {r : Record} {s : RecordStore qᵢ}
               → r ∈Rs s
               → ¬ (r ←⋆ (Qc qᵢ))
  ¬r←⋆qᵢ {r = B b} (here empty vB) r←⋆qᵢ
    with vB
  ... | inj₂  ⟨ qᵢ←r₁ , 1≤rb ⟩ = ¬r←⋆r (here empty vB) (ssr r←⋆qᵢ qᵢ←r₁)

  ¬r←⋆qᵢ {r = B b} (here (insert s vR) vB) r←⋆q₁
    with vB
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₁ , rq<rb ⟩ ⟩ ⟩ = ¬r←⋆qᵢ q∈s (←⋆inv q←r₁ r←⋆q₁)
  ... | inj₂ ⟨ qᵢ←r₁ , 1≤rb ⟩ = ¬r←⋆r ((here (insert s vR) vB)) (ssr r←⋆q₁ qᵢ←r₁)

  ¬r←⋆qᵢ {r = Qc x₁} (here (insert s x) vQ) r₁←⋆qᵢ
    with vQ
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₁ , rb≡rq ⟩ ⟩ ⟩ = ¬r←⋆qᵢ b∈s (←⋆inv b←r₁ r₁←⋆qᵢ)

  ¬r←⋆qᵢ (there r' s v r∈s) r←⋆qᵢ = ¬r←⋆qᵢ r∈s r←⋆qᵢ


  -- Aux Lemma
  r₀←⋆r₁→rr₀≤rr₁ : {qᵢ : QC} {r₀ r₁ : Record} {s₀ s₁ : RecordStore qᵢ}
                 → r₀ ∈Rs s₀ → r₁ ∈Rs s₁
                 → r₀ ←⋆ r₁
                 → round r₀ ≤ round r₁ ⊎ HashBroke
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b}  r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
    with v₁
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₁ , rq<rb ⟩ ⟩ ⟩
      with ←inj r₀←r₁ q←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl            = inj₁ (<⇒≤ rq<rb)
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b}  r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
      | inj₂  ⟨ qᵢ←r₁ , 1≤rb ⟩
      with ←inj r₀←r₁ qᵢ←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl            = {!!} --inj₁ (<⇒≤ rq<rb) -- I need that : round qᵢ = 0

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = Qc q} r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
    with v₁
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₁ , refl ⟩ ⟩ ⟩
     with ←inj r₀←r₁ b←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl            = inj₁ ≤-refl

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b}  r₀∈s (here s₁ v₁) (ssr r₀←⋆r₁ r₀←r₁)
     with v₁
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₁ , rq<rb ⟩ ⟩ ⟩
      with ←inj r₀←r₁ q←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl
        with r₀←⋆r₁→rr₀≤rr₁ r₀∈s q∈s r₀←⋆r₁
  ...     | inj₁ rr₀≤rq        = inj₁ (≤-trans rr₀≤rq (<⇒≤ rq<rb))
  ...     | inj₂ hashbroke     = inj₂ hashbroke
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b} r₀∈s (here s₁ v₁) (ssr r₀←⋆r₁ r₀←r₁)
      | inj₂ ⟨ qᵢ←r₁ , 1≤rb ⟩
      with ←inj r₀←r₁ qᵢ←r₁
  ... | inj₁ refl              = ⊥-elim (¬r←⋆qᵢ r₀∈s r₀←⋆r₁)
  ... | inj₂ hashbroke         = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = Qc q} r₀∈s (here s₁ v₁) (ssr r₀←⋆r₁ r₀←r₁)
    with v₁
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₁ , refl ⟩ ⟩ ⟩
     with ←inj r₀←r₁ b←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl
        with r₀←⋆r₁→rr₀≤rr₁ r₀∈s b∈s r₀←⋆r₁
  ...     | inj₂ hashbroke     = inj₂ hashbroke
  ...     | inj₁ rr₀≤rb        = inj₁ rr₀≤rb

  r₀←⋆r₁→rr₀≤rr₁ r₀∈s (there r' s v r₁∈s) r₀←⋆r₁ = r₀←⋆r₁→rr₀≤rr₁ r₀∈s r₁∈s r₀←⋆r₁



  round-mono : ∀  {qᵢ : QC} {r₀ r₁ r₂ : Record} {s₀ s₁ s₂ : RecordStore qᵢ}
                 → r₀ ∈Rs s₀ → r₁ ∈Rs s₁ → r₂ ∈Rs s₂
                 → r₀ ←⋆ r₂ → r₁ ←⋆ r₂
                 → round r₀ < round r₁
                 → (r₀ ←⋆ r₁) ⊎ HashBroke
  round-mono r₀∈s r₁∈s r₂∈s (ss0 r₀←r₂) (ss0 r₁←r₂) rr₀<rr₁
    with ←inj r₀←r₂ r₁←r₂
  ... | inj₁ refl                            = ⊥-elim (<⇒≢ rr₀<rr₁ refl)
  ... | inj₂ hashBroke                       = inj₂ hashBroke

  round-mono  {r₁ = r₁} r₀∈s r₁∈s r₂∈s (ss0 r₀←r₂) (ssr r₁←⋆r r←r₂) rr₀<rr₁
    with ←inj r₀←r₂ r←r₂
  ... | inj₂ hashBroke                       = inj₂ hashBroke
  ... | inj₁ refl
      with r₀←⋆r₁→rr₀≤rr₁ r₁∈s r₀∈s r₁←⋆r
  ...   |  inj₁ rr₁≤rr₀                      = ⊥-elim (≤⇒≯ rr₁≤rr₀ rr₀<rr₁)
  ...   |  inj₂ hashbroke                    = inj₂ hashbroke

  round-mono r₀∈s r₁∈s r₂∈s (ssr r₀←⋆r r←r₂) (ss0 r₁←r₂)        rr₀<rr₁
     with ←inj r₁←r₂ r←r₂
  ... | inj₂ hashBroke                       = inj₂ hashBroke
  ... | inj₁ refl                            = inj₁ r₀←⋆r

  round-mono {r₂ = B b} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with v
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₂ , rq<rb ⟩ ⟩ ⟩
       with ←inj r←r₂ q←r₂ | ←inj rₓ←r₂ q←r₂
  ...    | _                | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₂ hashbroke   | _              = inj₂ hashbroke
  ...    | inj₁ refl        | inj₁ refl      = round-mono r₀∈s r₁∈s q∈s r₀←⋆r r₁←⋆rₓ rr₀<rr₁
  round-mono {r₂ = B b} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
      | inj₂  ⟨ qᵢ←r₂ , 1≤rb ⟩
         with ←inj r←r₂ qᵢ←r₂
  ...      | inj₂ hashbroke                  = inj₂ hashbroke
  ...      | inj₁ refl                       = ⊥-elim (¬r←⋆qᵢ r₀∈s r₀←⋆r)

  round-mono {r₂ = Qc q} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with v
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₂ , rb<rq ⟩ ⟩ ⟩
       with ←inj r←r₂ b←r₂ | ←inj rₓ←r₂ b←r₂
  ...    | _                | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₂ hashbroke   | _              = inj₂ hashbroke
  ...    | inj₁ refl        | inj₁ refl      = round-mono r₀∈s r₁∈s b∈s r₀←⋆r r₁←⋆rₓ rr₀<rr₁

  round-mono r₀∈s r₁∈s (there r' s v r₂∈s) r₀←⋆r₂ r₁←⋆r₂ rr₀<rr₁
                                             = round-mono r₀∈s r₁∈s r₂∈s r₀←⋆r₂ r₁←⋆r₂ rr₀<rr₁




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

