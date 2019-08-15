open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (Decidable)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.List.Any
open import Data.List.All
open import Data.Maybe
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction; contraposition)


open import Data.Fin using (Fin ; fromℕ≤; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Vec hiding (insert) renaming (lookup to lookupVec; allFin to allFinVec; map to mapVec; take to takeVec; tabulate to tabulateVec)
open import Data.Vec.Bounded renaming (filter to filterVec) hiding ([] ; _∷_)
open import Data.Vec.Relation.Unary.Any renaming (Any to AnyVec ; any to anyVec)
open import Data.Vec.Relation.Unary.All renaming (All to AllVec ; all to allVec)
open import Data.Vec.Properties
open import Hash
open import Lemmas
open import Level using (0ℓ)

module LibraBFT
  -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open WithCryptoHash hash hash-cr

 ------------------------- AuxTypes ----------------------------
  Author : Set
  Author = ℕ

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

  record Timeout : Set where
    constructor mkTimeout
    field
      toEpochId : EpochId
      toRound   : Round
      toAuthor  : Author
      --toSignature : Signature

  data Record : Set where
    B  : Block   → Record
    Q  : QC      → Record
    -- vote    : Vote    → Record
    -- timeout : Timeout → Record

  data HashOrRec : Set where
   horRec  : Record → HashOrRec
   horHash : Hash   → HashOrRec

  round : Record → Round
  round (B b)  = Block.round b
  round (Q q) = QC.round q

  prevHash : Record → Hash
  prevHash (B b)  = Block.prevQCHash b
  prevHash (Q q) = QC.blockHash q




  data RecOrInit : Set where
    I : Initial → RecOrInit
    R : Record  → RecOrInit



 -- Hash Functions ----------------------------------------------
  postulate
    encodeR     : RecOrInit → ByteString
    encodeR-inj : ∀ {r₀ r₁ : RecOrInit} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR = hash ∘ encodeR


  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  data _←_ : RecOrInit → RecOrInit → Set where
    i←B : ∀ {i : Initial} {b : Block}
          → HashR (I i) ≡  Block.prevQCHash b
          → I i ← R (B b)
    Q←B : ∀ {q : QC} {b : Block}
          → HashR (R (Q q)) ≡  Block.prevQCHash b
          → R (Q q) ← R (B b)
    B←Q : ∀ {b : Block} {q : QC}
          → HashR (R (B b)) ≡ QC.blockHash q
          → R (B b) ← R (Q q)

  data _←⋆_ (r₁ r₂ : RecOrInit) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : RecOrInit} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂


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

  hᵢ←⋆R (there _ s _ r∈s) = hᵢ←⋆R r∈s
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



  -- 2
  -- I think we should prove injectivity in Record Chains instead
  ←inj : ∀ {r₀ r₁ r₂ : RecOrInit} → (r₀ ← r₂) → (r₁ ← r₂)
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
  r₀←⋆r₁→rr₀≤rr₁ r₀∈s (there r' s v r₁∈s) r₀←⋆r₁
                               = r₀←⋆r₁→rr₀≤rr₁ r₀∈s r₁∈s r₀←⋆r₁
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
  ...    | inj₂ hashbroke  | inj₁ _         = inj₂ hashbroke
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
  ...    | inj₂ hashbroke  | inj₁ _         = inj₂ hashbroke
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

  NodeTime : Set
  NodeTime = {!!}
    

  FakeTypeActiveNodes : Set
  -- Paper says HashSet<Author>

  OneSender : Set
  OneSender = Author × Round

  LatestSenders : Set
  LatestSenders = List OneSender  -- Paper says Vec, but I think List may suffice for us and is easier to deal with

  Duration : Set
  Duration = ℕ

  {- Couldn't make Float work, keep as ℕ for now
     See: https://agda.readthedocs.io/en/v2.6.0.1/language/built-ins.html#floats
     postulate Float : Set
     {-# BUILTIN FLOAT Float #-}
  -}

  GammaType : Set
  GammaType = ℕ  -- Should be Float, but see above comment

  

  -- Section 7.9, page 26
  record PacemakerState : Set where
    field
      pmsActiveRound       : Round
      pmsActiveLeader      : Maybe Author
      pmsActiveRoundStart  : NodeTime
      pmsActiveNodes       : FakeTypeActiveNodes
      pmsBroadcastInterval : Duration
      pmsDelta             : Duration
      pmsGamma             : GammaType

  open PacemakerState

  -- Section 5.6, page 17
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


      nsRecordStore         : RecordStoreState
      nsPaceMaker           : PacemakerState
      nsEpochId             : EpochId
      nsLocalAuthor         : Author
      -- nsLatestVotedRound : Round
      nsLockedRound         : Round
      nsLatestBroadcast     : NodeTime
      -- nsLatestSenders    : LatestSenders
      -- nsTracker          : DataTracker
      -- nsPastRecordStores : EpochId → RecordStoreState  -- How to model map?  AVL?  Homegrown?

  open NodeState

-------------------- Properties of Authors  ---------------------

  -- TODO: After merging with Lisandra: add au prefix to Author fields, and put this after definitions
  data Either {A : Set} {B : Set} : Set where
    left  : ∀ (x : A) → Either {A} {B}
    right : ∀ (x : B) → Either {A} {B}

  left-inj  : ∀ {n₁ : ℕ} {n₂ : ℕ} → left  n₁ ≡ left  {ℕ} {ℕ} n₂ → n₁ ≡ n₂
  left-inj refl = refl

  right-inj : ∀ {n₁ : ℕ} {n₂ : ℕ} → right n₁ ≡ right {ℕ} {ℕ} n₂ → n₁ ≡ n₂
  right-inj refl = refl

  data isLeft {A : Set} {B : Set} : Either {A} {B} → Set where
    ll : ∀ (x : A) → isLeft (left x)

  data isRight {A : Set} {B : Set} : Either {A} {B} → Set where
    rr : ∀ (x : B) → isRight (right x)

  _ : left 1 ≡ left 1 -- Passes but leaves unresolved meta warning for the B type
  _ = refl

  _ : left {B = Bool} 1 ≡ left 1 -- Specifying a type for B eliminates said warning
  _ = refl

  AuthorHonest? : Set
  AuthorHonest? = Either {Author} {Author}

  authorOf : AuthorHonest? → Author
  authorOf (left x)  = x
  authorOf (right x) = x

  dummyAuthor : ℕ → Author
  dummyAuthor i = i

  _ : authorOf (left (dummyAuthor 0)) ≡ authorOf (right (dummyAuthor 0))
  _ = refl

  _ : authorOf (left (dummyAuthor 0)) ≢ authorOf (right (dummyAuthor 1))
  _ = λ ()

  -- The first n - f authors are honest, the rest are not
  dummyAuthorHonest? : ℕ → ℕ → ℕ → AuthorHonest?
  dummyAuthorHonest? n f i with i + f <? n
  ...| yes _ = right {Author} {Author} (dummyAuthor i)
  ...| no _  = left  {Author} {Author} (dummyAuthor i)

  _ : dummyAuthorHonest? 4 1 3 ≡ (left (dummyAuthor 3))
  _ = refl

  _ : dummyAuthorHonest? 4 1 0 ≡ (right (dummyAuthor 0))
  _ = refl

  dummyAuthors : (n : ℕ) → (f : ℕ) → Vec AuthorHonest? n
  dummyAuthors n f = tabulateVec ((dummyAuthorHonest? n f) ∘ toℕ)

  _≡-AuthorHonest?_ : AuthorHonest? → AuthorHonest? → Set
  a₁ ≡-AuthorHonest? a₂ = a₁ ≡ a₂

  _≟-AuthorHonest?_ : (a₁ : AuthorHonest?) → (a₂ : AuthorHonest?) → Dec (a₁ ≡ a₂)
  (left  n₁) ≟-AuthorHonest? (right n₂) = no (λ ())
  (right n₁) ≟-AuthorHonest? (left  n₂) = no (λ ())
  (right n₁) ≟-AuthorHonest? (right n₂) with n₁ ≟ n₂
  ...| yes xx = yes (cong right xx)
  ...| no  xx = no ( λ x → xx (right-inj {n₁} {n₂} x))
  (left  n₁) ≟-AuthorHonest? (left  n₂) with n₁ ≟ n₂
  ...| yes xx = yes (cong left xx)
  ...| no  xx = no ( λ x → xx (left-inj  {n₁} {n₂} x))


---------------------- Epoch Configuration  ---------------------

  data DistinctVec {ℓ} {A} (_P_ : A → A → Set ℓ) {n} (v : Vec {ℓ} A n) : Set (Level.suc ℓ) where
    distinct : AllVec (λ i → (AllVec (λ j → i ≡ j ⊎ (¬ (lookupVec v i) P (lookupVec v j))) (allFinVec n))) (allFinVec n)
             → DistinctVec _P_ v

  record EpochConfiguration : Set (Level.suc Level.zero) where
    field
      f : ℕ                               -- Maxiumum number of faulty nodes in this epoch
      n : ℕ                               -- Total number of nodes who can vote in this epoch
      3f<n : 3 * f < n                    -- Require n > 3 * f
      votingRights : Vec AuthorHonest? n  -- Lefts are bad guys, Rights are good guys
      votersDistinct : DistinctVec {Level.zero} {AuthorHonest?} _≡-AuthorHonest?_ {n} votingRights
                                          -- For now we consider all "active" authors have equal voting rights

  open EpochConfiguration

  -- Test data

  testN = 4
  testF = 1

  _ : Data.Vec.lookup (dummyAuthors testN testF) (Data.Fin.fromℕ≤ {3} (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ dummyAuthorHonest? testN testF 3
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN testF) (Data.Fin.fromℕ≤ {2} (s≤s (s≤s (s≤s z≤n))))       ≡ dummyAuthorHonest? testN testF 2
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN testF) (Data.Fin.fromℕ≤ {1} (s≤s (s≤s z≤n)))             ≡ dummyAuthorHonest? testN testF 1
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN testF) (Data.Fin.fromℕ≤ {0} (s≤s z≤n))                   ≡ dummyAuthorHonest? testN testF 0
  _ = refl

  dummyAuthorsDistinct : ∀ (n : ℕ) → (f : ℕ) → DistinctVec {Level.zero} _≡-AuthorHonest?_ (dummyAuthors n f)
  dummyAuthorsDistinct 0 _ = distinct []
  dummyAuthorsDistinct (suc n) f
     with allFinVec (suc n)
  ...| x ∷ xs = {!!}


  3*testF<testN : (3 * testF) < testN
  3*testF<testN = s≤s (s≤s (s≤s (s≤s z≤n)))

  ec1 : EpochConfiguration
  ec1 = record {
          f                = testF
        ; n                = testN
        ; 3f<n             = 3*testF<testN
        ; votingRights     = dummyAuthors testN testF
        ; votersDistinct   = dummyAuthorsDistinct testN testF
        }

  ------------------------- End test data ----------------------

  isVoter? : (ec : EpochConfiguration)
           → (a : AuthorHonest?)
           → Dec (AnyVec (a ≡-AuthorHonest?_) (votingRights ec))
  isVoter? ec a = anyVec (a ≟-AuthorHonest?_) {n ec} (votingRights ec)

  isVoter : (ec : EpochConfiguration) → (a : Author) → Bool
  isVoter ec a with
    isVoter? ec (left {Author} {Author} a) | isVoter? ec (right {Author} {Author} a)
  ...| no  _ | no _  = false
  ...| yes _ | no _  = true
  ...| _     | yes _ = true

  _ : (left {B = Author} (dummyAuthor 0)) ≡ left (dummyAuthor 0)
  _ = refl

  _ : lookupVec (votingRights ec1) (Data.Fin.fromℕ≤ (s≤s z≤n))                   ≡ right (dummyAuthor 0)
  _ = refl

  _ : lookupVec (votingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s z≤n)))             ≡ right (dummyAuthor 1)
  _ = refl

  _ : lookupVec (votingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s z≤n))))       ≡ right (dummyAuthor 2)
  _ = refl

  _ : lookupVec (votingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ left  (dummyAuthor 3)
  _ = refl

  _ : isVoter ec1 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isVoter ec1 (dummyAuthor 3) ≡ true
  _ = refl

  _ : isVoter ec1 (dummyAuthor 5) ≡ false
  _ = refl

  isHonest? : (a  : AuthorHonest?)
            → Dec (isRight a)
  isHonest? (left x)  = no (λ ())
  isHonest? (right x) = yes (rr x)

  isHonestP : (ec : EpochConfiguration)
            → (a  : Author)
            → Bool
  isHonestP ec a with isVoter? ec (right {Author} {Author} a)
  ...| yes _ = true
  ...| no  _ = false

  _ : isHonestP ec1 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isHonestP ec1 (dummyAuthor 1) ≡ true
  _ = refl

  _ : isHonestP ec1 (dummyAuthor 2) ≡ true
  _ = refl

  _ : isHonestP ec1 (dummyAuthor 3) ≡ false
  _ = refl

  _ : isHonestP ec1 (dummyAuthor 5) ≡ false
  _ = refl

  -- TODO: we need to state the BFT assumption (that there are at most f bad guys, or equivalently,
  -- at least n - f good guys), so that we can used it in proofs.  It would be good to do this in a
  -- way that abstract away from the particular representation of EpochConfiguration.  Here is an
  -- attempt, using the isHonest? decidable instance.  I can't get it to typecheck though.  I am not
  -- sure how to import and instantiate the anonymous module in Data.Vec.Bounded in order to provide
  -- the right predicate to filter (renamed to filterVec here), and there seems to be some issue
  -- related to levels but I haven't figured it out after a bit of mucking around.
  {-
  BFTAssumption : (ec : EpochConfiguration)
    → Data.Vec.Bounded.Vec≤.length (filterVec {P = isHonest? ec} (Data.Vec.Bounded.fromVec (votingRights ec))) > (n ec) ∸ (f ec)
  BFTAssumption = {!!}
  -}

---------------------- Update Skeleton ----------------

  SmrContext : Set
  SmrContext = {!!}

  record NodeUpdateActions : Set where
    constructor mkNodeUpdateAction
    field
      nuaShouldScheduleUpdate : Maybe NodeTime
      nuaShouldNotifyLeader   : Maybe Author
      nuaShouldBroadcast      : Bool

  open NodeUpdateActions

  NodeUpdateActions∷new : NodeUpdateActions
  NodeUpdateActions∷new = mkNodeUpdateAction nothing nothing false

  -- Section 7.3, page 23
  record PacemakerUpdateActions : Set where
    constructor mkPacemakerUpdateActions
    field
      puaShouldScheduleUpdate : Maybe NodeTime
      puaShouldCreateTimeout  : Maybe Round
      puaShouldNotifyLeader   : Maybe Author
      puaShouldBroadcast      : Bool
      puaShouldProposeBlock   : Maybe QCHash

  open PacemakerUpdateActions

  PacemakerUpdateActions∷new : PacemakerUpdateActions
  PacemakerUpdateActions∷new =
    mkPacemakerUpdateActions
      nothing nothing nothing false nothing

------------- Musings about high-level state for proving properties -------

  -- Nothing here yet, just placeholders
  -- This will model the NodeStates for each Author.  Eventually, we will
  -- define executions of the system, so that we can prove properties like
  -- invariants (in every execution, every honest node's state has certain
  -- properties, etc.).  This will require us to track node states and
  -- state machine contexts for each participant (Author)
  data AuthorNodeStates : Set where
  data AuthorStateMachineContexts : Set where

------------------------------- Pseudomonad --------------------------------

  -- In an effort to make our Agda proofs mirror the Haskell code Harold is
  -- writing, I came to realise that we'd need some Monad-like notion for
  -- representing the environment and states of various participants.  I see
  -- that there is some explicit support for Monad-like functionality in the
  -- Agda standard library:
  --   https://github.com/agda/agda-stdlib/blob/v1.0/src/Data/Container/FreeMonad.agda  -- and also some syntactic sugar for do notation:
  --   https://agda.readthedocs.io/en/v2.6.0.1/language/syntactic-sugar.html
  -- However, I want to discuss this first with Victor and have not spent time
  -- to learn about it, so initially I am contonuing with my "poor person's"
  -- version to make progress and develop intuition.

  -- Nothing here yet, just a placeholder
  -- This will likely model a set of messages, but we will need to think about
  -- the communication model to decide more detail, such as whether we will
  -- allow message duplication, loss, reodering, etc.
  data CommunicationEnvironment : Set where

  -- This is not really a monad as such; we will pass these around explicitly,
  -- getting new versions back, allowing us to model side effects, but only
  -- relative to the explicitly constructed PseudoMonad.  This probably won't
  -- last long, but is what am exploring as a first cut.  So far, I think we
  -- may need to send messages and update our nodestate via this "monad".
  record PseudoMonad : Set where
    field
      commEnv    : CommunicationEnvironment
      -- TODO: what other side effects might we need to track?

  createTimeoutCond'' : ∀ {h} → RecordStore h → Author → Maybe Round → SmrContext → RecordStore h
  createTimeoutCond'' rs _ nothing  _ = rs
  createTimeoutCond'' rs _ (just r) _ = {!!} -- insert rs {!!} {!!}

  createTimeoutCond' : RecordStoreState → Author → Maybe Round → SmrContext → RecordStoreState
  createTimeoutCond' rss a mbr smr =
    record rss { recStore = createTimeoutCond'' {RecordStoreState.sᵢ rss} (RecordStoreState.recStore rss) a mbr smr }

  -- TODO: I don't think we'll literally put Timeouts in RecordStore; see email (subject "Lemma S1 does not hold!" ...)
  createTimeoutCond : NodeState → Author → Maybe Round → SmrContext → NodeState
                                                                      -- TODO: after mering with Lisandra, naming conventions
  createTimeoutCond ns a r smr = record ns { nsRecordStore = createTimeoutCond' (NodeState.nsRecordStore ns) a r smr }

  -- fn process_pacemaker_actions( &mut self,
  --                               pacemaker_actions: PacemakerUpdateActions,
  --                               smr_context: &mut SMRContext,
  --                             ) -> NodeUpdateActions {
  processPacemakerActions :
      NodeState
    → PacemakerUpdateActions
    → SmrContext
    → NodeState × SmrContext × NodeUpdateActions
  processPacemakerActions self₀ pacemakerActions smrContext₀ =
    let
  -- let mut actions = NodeUpdateActions::new();
      actions = record NodeUpdateActions∷new {
  -- actions.should_schedule_update = pacemaker_actions.should_schedule_update;
                    nuaShouldScheduleUpdate = puaShouldScheduleUpdate pacemakerActions
  -- actions.should_broadcast = pacemaker_actions.should_broadcast;
                  ; nuaShouldBroadcast      = puaShouldBroadcast pacemakerActions
  -- actions.should_notify_leader = pacemaker_actions.should_notify_leader;
                  ; nuaShouldNotifyLeader   = puaShouldNotifyLeader pacemakerActions
                }


  -- if let Some(round) = pacemaker_actions.should_create_timeout {
  --   self.record_store.create_timeout(self.local_author, round, smr_context);
  -- }
      la₀   = nsLocalAuthor self₀
      round = puaShouldCreateTimeout pacemakerActions
      self₁ = createTimeoutCond self₀ la₀ round smrContext₀

  -- if let Some(previous_qc_hash) = pacemaker_actions.should_propose_block {
  --   self.record_store.propose_block(
  --       self.local_author,
  --       previous_qc_hash,
  --       self.latest_broadcast,
  --       smr_context,
  --   );
      previousQCHashMB = puaShouldProposeBlock pacemakerActions
      lb₀ = nsLatestBroadcast self₀
      -- TODO: we may need to modify the SMR context inside proposeBlock.  It's going to get
      -- painful here, as we will need to update both self amd SMR Context, based on the same
      -- condition



  -- }
  -- actions
  -- } }

    in {!!}

  -- fn update_node(&mut self, clock: NodeTime, smr_context: &mut SMRContext) -> NodeUpdateActions {
  updateNode : NodeState
             → NodeTime
             → SmrContext
             → NodeState × SmrContext × NodeUpdateActions
  updateNode self₀ clock smrContext₀ =
    let

  -- let latest_senders = self.read_and_reset_latest_senders();
         latestSenders = {!!}

  -- let pacemaker_actions = self.pacemaker.update_pacemaker( self.local_author, &self.record_store, self.latest_broadcast, latest_senders, clock,);
         pacemakerActions = {!!}

-- let mut actions = self.process_pacemaker_actions(pacemaker_actions, smr_context);
         -- Can't keep this organized as in paper, because can't do with & where here
         (self₁ , actions₀) = processPacemakerActions self₀ pacemakerActions smrContext₀

-- // Update locked round.
  -- self.locked_round = std::cmp::max(self.locked_round, self.record_store.highest_2chain_head_round());
  -- // Vote on a valid proposal block designated by the pacemaker, if any.
  -- if let Some((block_hash, block_round, proposer)) = self.record_store.proposed_block(&self.pacemaker) {
  --   // Enforce voting constraints.
  --   if block_round > self.latest_voted_round && self.record_store.previous_round(block_hash) >= self.locked_round {
  --     // Update latest voted round.
  --     self.latest_voted_round = block_round;
  --     // Try to execute the command contained the a block and create a vote.
  --     if self.record_store.create_vote(self.local_author, block_hash, smr_context) {
  --     // Ask that we reshare the proposal.
  --     actions.should_broadcast = true;
  --     // Ask to notify and send our vote to the author of the block.
  --     actions.should_notify_leader = Some(proposer);
  -- } } }
  -- // Check if our last proposal has reached a quorum of votes and create a QC.
  -- if self.record_store.check_for_new_quorum_certificate(self.local_author, smr_context) {
  --   // The new QC may cause a change in the pacemaker state: schedule a new run of this handler now.
  --   actions.should_schedule_update = Some(clock);
  -- }
  -- // Check if our last proposal has reached a quorum of votes and create a QC.
  -- if self.record_store.check_for_new_quorum_certificate(self.local_author, smr_context) {
  --   // The new QC may cause a change in the pacemaker state: schedule a new run of this handler now.
  --   actions.should_schedule_update = Some(clock);
  -- }
  -- // Check for new commits and verify if we should start a new epoch.
  -- for commit_qc in self
  --   .record_store
  --   .chain_between_quorum_certificates(
  --      self.tracker.highest_committed_round,
  --      self.record_store.highest_committed_round(),
  --   ) .cloned() {
  --   // Deliver the new committed state, together with a short certificate (if any).
  --   smr_context.commit(&commit_qc.state, self.record_store.commit_certificate(&commit_qc));
  --   // If the current epoch ended..
  --   let epoch_id = smr_context.read_epoch_id(&commit_qc.state);
  --   if self.epoch_id != epoch_id {
  --     // .. create a new record store and switch to the new epoch.
  --     self.start_new_epoch(epoch_id, commit_qc, smr_context);
  --     // .. stop delivering commits after an epoch change.
  --     break;
  -- } }
  -- // Update the data tracker and ask that we reshare data if needed.
  -- if self.tracker.update_and_decide_resharing(self.epoch_id, &self.record_store) {
  --   actions.should_broadcast = true;
  -- }
  -- // Return desired node actions to environment.
  -- actions

         nsFinal = {!!}
         smrContextFinal = {!!}
         actionsFinal = {!!}

    in
      (nsFinal , ( smrContextFinal , actionsFinal ))


  newPMSValue : PacemakerState → Round → NodeTime → PacemakerState
  newPMSValue self activeRound clock = record self {
  --    // .. store the new value
  --    self.active_round = active_round;
                    pmsActiveRound = activeRound
  --    // .. start a timer
  --    self.active_round_start = clock;
                  ; pmsActiveRoundStart = clock
  --    // .. recompute the leader
  --    self.active_leader = Some(Self::leader(record_store, active_round));
                  ; pmsActiveLeader = just {!!}
  --    // .. reset the set of nodes known to have entered this round (useful for leaders).
  --    self.active_nodes = HashSet::new();
                  ; pmsActiveNodes = {!!}
                  }
  --  }

  updatePMSandPUA : PacemakerState → PacemakerUpdateActions → Round → NodeTime
     → PacemakerState × PacemakerUpdateActions
  updatePMSandPUA s a ar cl
    -- // If the active round was just updated..
    -- if active_round > self.active_round { // .. store the new value
    with (ar >? (pmsActiveRound s))
                              -- // .. notify the leader to be counted as an "active node".
                              -- actions.should_notify_leader = self.active_leader;
  ...| yes _ = (newPMSValue s ar cl , record a { puaShouldNotifyLeader = {!!} })
  ...| no  _ = (s , a)


  -- Section 7.10, page 27
  -- fn update_pacemaker(
  --     &mut self,
  --     local_author: Author,
  --     record_store: &RecordStore,
  --     mut latest_broadcast: NodeTime,
  --     latest_senders: Vec<(Author, Round)>,
  --     clock: NodeTime,
  -- ) -> PacemakerUpdateActions {

  updatePacemaker : PacemakerState
                   → Author
                   → {h : Initial}
                   → RecordStore h
                   → NodeTime
                   → LatestSenders
                   → NodeTime
                   → PacemakerState × PacemakerUpdateActions
  updatePacemaker self₀ localAuthor recordStore latestBroadcast₀ latestSenders clock =

     let
  --  // Initialize actions with default values.
  --  let mut actions = PacemakerUpdateActions::new();
       actions₀ = PacemakerUpdateActions∷new

  --  // Recompute the active round.
  --  let active_round = std::cmp::max(record_store.highest_quorum_certificate_round(), record_store.highest_timeout_certificate_round(),) + 1;
       activeRound = {!!}

       (self₁ , actions₁) = updatePMSandPUA self₀ actions₀ activeRound clock

  --  // Update the set of "active nodes", i.e. received synchronizations at the same active round.
  --  for (author, round) in latest_senders {
  --    if round == active_round {
  --      self.active_nodes.insert(author);
  --  } }
  --  // If we are the leader and have seen a quorum of active node..
  --  if self.active_leader == Some(local_author)
  --    && record_store.is_quorum(&self.active_nodes)
  --    && record_store.proposed_block(&*self) == None {
  --    // .. propose a block on top of the highest QC that we know.
  --    actions.should_propose_block = Some(record_store.highest_quorum_certificate_hash().clone());
  --    // .. force an immediate update to vote on our own proposal.
  --    actions.should_schedule_update = Some(clock);
  --  }
  --  // Enforce sufficiently frequent broadcasts.
  --  if clock >= latest_broadcast + self.broadcast_interval {
  --    actions.should_broadcast = true;
  --    latest_broadcast = clock;
  --  }
  -- // If we have not yet, create a timeout after the maximal duration for rounds.
  -- let deadline = if record_store.has_timeout(local_author, active_round) {
  --                  NodeTime::never()
  --                } else {
  --                  self.active_round_start + self.duration(record_store, active_round)
  --                };
  -- if clock >= deadline {
  --   actions.should_create_timeout = Some(active_round);
  --   actions.should_broadcast = true;
  -- }
  -- // Make sure this update function is run again soon enough.
  -- actions.should_schedule_update = Some(std::cmp::min(
  --    actions.should_schedule_update.unwrap_or(NodeTime::never()),
  --    std::cmp::min(latest_broadcast + self.broadcast_interval, deadline),
  -- ));
  -- actions

       pmFinal      = {!!}
       actionsFinal = {!!}
     in ( pmFinal , actionsFinal )


