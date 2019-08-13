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
open import Lemmas

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

  EpochId : Set
  EpochId = ℕ

  Round : Set
  Round = ℕ

  Command : Set
  Command = ℕ

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

  record Initial : Set where
    field
      epochId : EpochId
      seed    : ℕ

  data Record : Set where
    B  : Block   → Record
    Q : QC      → Record
    -- vote    : Vote    → Record
    -- timeout : Timeout → Record



  round : Record → Round
  round (B b)  = Block.round b
  round (Q q) = QC.round q

  prevHash : Record → Hash
  prevHash (B b)  = Block.prevQCHash b
  prevHash (Q q) = QC.blockHash q




  data RecordChain : Set where
    I : Initial → RecordChain
    R : Record  → RecordChain



 -- Hash Functions ----------------------------------------------
  postulate
    encodeR     : RecordChain → ByteString
    encodeR-inj : ∀ {r₀ r₁ : RecordChain} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR = hash ∘ encodeR


  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  data _←_ : RecordChain → RecordChain → Set where
    i←B : ∀ {i : Initial} {b : Block}
          → HashR (I i) ≡  Block.prevQCHash b
          → I i ← R (B b)
    Q←B : ∀ {q : QC} {b : Block}
          → HashR (R (Q q)) ≡  Block.prevQCHash b
          → R (Q q) ← R (B b)
    B←Q : ∀ {b : Block} {q : QC}
          → HashR (R (B b)) ≡ QC.blockHash q
          → R (B b) ← R (Q q)

  data _←⋆_ (r₁ r₂ : RecordChain) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : RecordChain} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂


----------------------------------------------------------------


------------------------- RecordStore --------------------------

  data RecordStore (sᵢ : Initial) : Set

  Valid : {sᵢ : Initial} → Record → RecordStore sᵢ → Set

  data RecordStore sᵢ where
    empty  : RecordStore sᵢ
    insert : {r : Record} (s : RecordStore sᵢ)
             → Valid r s → RecordStore sᵢ


  data _∈Rs_ {sᵢ} (r : Record) : RecordStore sᵢ → Set where
    here  : ∀ (s : RecordStore sᵢ) (v : Valid r s) → r ∈Rs (insert s v)
    there : ∀ (r' : Record) (s : RecordStore sᵢ) (v : Valid r' s)
           → r ∈Rs s
           → r ∈Rs (insert s v)


  ValidBlock : {sᵢ : Initial} → Block → RecordStore sᵢ → Set
  ValidBlock {sᵢ} b rs =  ∃[ q ] ( q ∈Rs rs × R q ← R (B b) × round q < round (B b) )
                           ⊎
                           (I sᵢ) ← R (B b) × 1 ≤ round (B b)


  Valid (B b) rs = ValidBlock b rs
  Valid (Q q) rs = ∃[ b ] ( b ∈Rs rs × R b ← R (Q q) × round (Q q) ≡ round b )



-- Lemma S₁ ---------------------------------------------------

  -- 1
  hᵢ←⋆R : ∀ {sᵢ : Initial} {r : Record} {s : RecordStore sᵢ}
          → r ∈Rs s
          → (I sᵢ) ←⋆ R r
  hᵢ←⋆R {r = B b} (here empty vB)
    with vB
  ... | inj₂  ⟨ sᵢ←B , 1≤rB ⟩ = ss0 sᵢ←B

  hᵢ←⋆R {r = B b} (here (insert s x) vB)
     with vB
  ... | inj₁ ⟨ q , ⟨ q∈rs , ⟨ q←B , snd ⟩ ⟩ ⟩ = ssr (hᵢ←⋆R q∈rs) q←B
  ... | inj₂ ⟨ sᵢ←B , 1≤rB ⟩                  = ss0 sᵢ←B

  hᵢ←⋆R {r = Q q} (here s vQ)
    with vQ
  ... |       ⟨ b , ⟨ b∈rs , ⟨ b←Q , snd ⟩ ⟩ ⟩ = ssr (hᵢ←⋆R b∈rs) b←Q

  hᵢ←⋆R (there r' s v r∈s) = hᵢ←⋆R r∈s


  -- 2
  -- I think we should prove injectivity in Record Chains instead
  ←inj : ∀ {r₀ r₁ r₂ : RecordChain} → (r₀ ← r₂) → (r₁ ← r₂)
           → r₀ ≡ r₁ ⊎ HashBroke
  ←inj {i₀} {i₁} {b} (i←B i₀←b) (i←B i₁←b)
    with hash-cr (trans i₀←b (sym i₁←b))
  ... | inj₁ ⟨ i₀≢i₁ , hi₀≡hi₁ ⟩
             = inj₂ ⟨ ⟨ encodeR i₀ , encodeR i₁ ⟩ , ⟨ i₀≢i₁ , hi₀≡hi₁ ⟩ ⟩
  ... | inj₂ i₀≡i₁
             = inj₁ (encodeR-inj i₀≡i₁)

  ←inj {i} {q} {b} (i←B i←b) (Q←B q←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ ⟨ i≢q , hi≡hq ⟩
             = inj₂ ⟨ ⟨ encodeR i , encodeR q ⟩ , ⟨ i≢q , hi≡hq ⟩ ⟩
  ... | inj₂ i≡q
             = contradiction (encodeR-inj i≡q) λ ()

  ←inj {q} {i} {b} (Q←B q←b) (i←B i←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ ⟨ i≢q , hi≡hq ⟩
             = inj₂ ⟨ ⟨ encodeR i , encodeR q ⟩ , ⟨ i≢q , hi≡hq ⟩ ⟩
  ... | inj₂ i≡q
             = contradiction (encodeR-inj i≡q) λ ()

  ←inj {q₀} {q₁} {b} (Q←B q₀←b) (Q←B q₁←b)
    with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩
             = inj₂ ⟨ ⟨ encodeR q₀ , encodeR q₁ ⟩ , ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩ ⟩
  ... | inj₂ q₁≡q₂
             = inj₁ (encodeR-inj q₁≡q₂)

  ←inj {b₀} {b₁} {q} (B←Q b₀←q) (B←Q b₁←q)
    with hash-cr (trans b₀←q (sym b₁←q))
  ... | inj₁ ⟨ b₀≢b₁ , hb₀←hb₁ ⟩
             = inj₂ ⟨ ⟨ encodeR b₀ , encodeR b₁ ⟩ , ⟨ b₀≢b₁ , hb₀←hb₁ ⟩ ⟩
  ... | inj₂ b₀≡b₁
             = inj₁ (encodeR-inj b₀≡b₁)


  -- 3
  -- Aux Lemma
  ¬r←⋆sᵢ : ∀  {sᵢ : Initial} {r : Record} {s : RecordStore sᵢ}
               → r ∈Rs s
               → ¬ (R r ←⋆ (I sᵢ))
  ¬r←⋆sᵢ r∈s (ss0 ())
  ¬r←⋆sᵢ r∈s (ssr r←⋆r₁ ())

  -- Aux Lemma
  r₀←⋆r₁→rr₀≤rr₁ : {sᵢ : Initial} {r₀ r₁ : Record} {s₀ s₁ : RecordStore sᵢ}
                 → r₀ ∈Rs s₀ → r₁ ∈Rs s₁
                 → R r₀ ←⋆ R r₁
                 → round r₀ ≤ round r₁ ⊎ HashBroke
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b}  r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
    with v₁
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₁ , rq<rb ⟩ ⟩ ⟩
      with ←inj r₀←r₁ q←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl            = inj₁ (<⇒≤ rq<rb)
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b}  r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
      | inj₂  ⟨ sᵢ←r₁ , 1≤rb ⟩
      with ←inj r₀←r₁ sᵢ←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = Q q} r₀∈s (here s₁ v₁) (ss0 r₀←r₁)
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
      | inj₂ ⟨ sᵢ←r₁ , 1≤rb ⟩
      with ←inj r₀←r₁ sᵢ←r₁
  ... | inj₁ refl              = ⊥-elim (¬r←⋆sᵢ r₀∈s r₀←⋆r₁)
  ... | inj₂ hashbroke         = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = Q q} r₀∈s (here s₁ v₁) (ssr r₀←⋆r₁ r₀←r₁)
    with v₁
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₁ , refl ⟩ ⟩ ⟩
     with ←inj r₀←r₁ b←r₁
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl
        with r₀←⋆r₁→rr₀≤rr₁ r₀∈s b∈s r₀←⋆r₁
  ...     | inj₂ hashbroke     = inj₂ hashbroke
  ...     | inj₁ rr₀≤rb        = inj₁ rr₀≤rb

  r₀←⋆r₁→rr₀≤rr₁ r₀∈s (there r' s v r₁∈s) r₀←⋆r₁
                               = r₀←⋆r₁→rr₀≤rr₁ r₀∈s r₁∈s r₀←⋆r₁



  round-mono : ∀  {sᵢ : Initial} {r₀ r₁ r₂ : Record} {s₀ s₁ s₂ : RecordStore sᵢ}
                 → r₀ ∈Rs s₀ → r₁ ∈Rs s₁ → r₂ ∈Rs s₂
                 → R r₀ ←⋆ R r₂ → R r₁ ←⋆ R r₂
                 → round r₀ < round r₁
                 → (R r₀ ←⋆ R r₁) ⊎ HashBroke
  round-mono r₀∈s r₁∈s r₂∈s (ss0 r₀←r₂) (ss0 r₁←r₂) rr₀<rr₁
     with ←inj r₀←r₂ r₁←r₂
  ... | inj₁ refl                           = ⊥-elim (<⇒≢ rr₀<rr₁ refl)
  ... | inj₂ hashBroke                      = inj₂ hashBroke

  round-mono  {r₁ = r₁} r₀∈s r₁∈s r₂∈s (ss0 r₀←r₂) (ssr r₁←⋆r r←r₂) rr₀<rr₁
     with ←inj r₀←r₂ r←r₂
  ... | inj₂ hashBroke                      = inj₂ hashBroke
  ... | inj₁ refl
      with r₀←⋆r₁→rr₀≤rr₁ r₁∈s r₀∈s r₁←⋆r
  ...   |  inj₁ rr₁≤rr₀                     = ⊥-elim (≤⇒≯ rr₁≤rr₀ rr₀<rr₁)
  ...   |  inj₂ hashbroke                   = inj₂ hashbroke

  round-mono r₀∈s r₁∈s r₂∈s (ssr r₀←⋆r r←r₂) (ss0 r₁←r₂)        rr₀<rr₁
     with ←inj r₁←r₂ r←r₂
  ... | inj₂ hashBroke                      = inj₂ hashBroke
  ... | inj₁ refl                           = inj₁ r₀←⋆r

  round-mono {r₂ = B b} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with v
  ... | inj₁ ⟨ q , ⟨ q∈s , ⟨ q←r₂ , rq<rb ⟩ ⟩ ⟩
       with ←inj r←r₂ q←r₂ | ←inj rₓ←r₂ q←r₂
  ...    | _               | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₂ hashbroke  | _              = inj₂ hashbroke
  ...    | inj₁ refl       | inj₁ refl      = round-mono r₀∈s r₁∈s q∈s r₀←⋆r r₁←⋆rₓ rr₀<rr₁
  round-mono {r₂ = B b} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
      | inj₂  ⟨ sᵢ←r₂ , 1≤rb ⟩
         with ←inj r←r₂ sᵢ←r₂
  ...      | inj₂ hashbroke                 = inj₂ hashbroke
  ...      | inj₁ refl                      = ⊥-elim (¬r←⋆sᵢ r₀∈s r₀←⋆r)

  round-mono {r₂ = Q x₁} r₀∈s r₁∈s (here s v) (ssr r₀←⋆r r←r₂) (ssr r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with v
  ... | ⟨ b , ⟨ b∈s , ⟨ b←r₂ , rb<rq ⟩ ⟩ ⟩
       with ←inj r←r₂ b←r₂ | ←inj rₓ←r₂ b←r₂
  ...    | _               | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₂ hashbroke  | _              = inj₂ hashbroke
  ...    | inj₁ refl       | inj₁ refl      = round-mono r₀∈s r₁∈s b∈s r₀←⋆r r₁←⋆rₓ rr₀<rr₁

  round-mono r₀∈s r₁∈s (there r' s v r₂∈s) r₀←⋆r₂ r₁←⋆r₂ rr₀<rr₁
                                            = round-mono r₀∈s r₁∈s r₂∈s r₀←⋆r₂ r₁←⋆r₂ rr₀<rr₁


----------------------------------------------------------------


------------------------ RecordStoreState ----------------------

  record RecordStoreState : Set where
    field
      epoch     : EpochId
      sᵢ        : Initial
      recStore  : RecordStore sᵢ
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


{-
  -- Other approaches for Record Store

  -- 1 - Record Store as a List of all Records and the set of Verified Records
  -- would be _∈Rs_

  Valid : QC → Record → List Record → Set
  Valid qᵢ (B b)  [] = Qc qᵢ ← B b × Block.round b ≡ 1
  Valid qᵢ (B b)  rs = ∃[ q ] ( q ∈ rs × q ← B b × round q < round (B b) )
                       ⊎
                       All (_< Block.round b)
                           (List-map round ( filter (λ r → prevHash (B b) ≟Hash prevHash r) rs ))
  Valid qᵢ (Qc q) rs = ∃[ b ] ( b ∈ rs × b ← Qc q × round (Qc q) ≡ round b )


  data ∈Rs (qᵢ : QC) (r : Record) : List Record → Set where
    here  : ∀ (s : List Record) (v : Valid qᵢ r s)
           → ∈Rs qᵢ r s
    there : ∀ (r' : Record) (s : List Record) (v : Valid qᵢ r' s)
           → ∈Rs qᵢ r s
           → ∈Rs qᵢ r (r' ∷ s)
-}
{-
  -- Like e Rose Tree of Valid Records
  data ValidRecord Record : Set

  data Valid Record : (List (ValidRecord Record)) → Set

  data ValidRecord  Record where
    insR : ∀ (r : Record) (s : List (ValidRecord Record)) → Valid Record s → ValidRecord Record


  Valid r [] = {!⊤!}
  Valid r (insR (B b) s v ∷ rs) =     r ← (B b)
                                   ×  Valid r rs
                                   ×  round r < Block.round b
  Valid r (insR (Qc q) s v ∷ rs) =  r ← (Qc q)
                                   ×  Valid r rs
                                   ×  round r ≡ QC.round q

-}


