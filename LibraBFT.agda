open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no)
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
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin ; fromℕ≤)
open import Data.Vec hiding (insert) renaming (lookup to lookupVec; allFin to allFinVec; take to takeVec; tabulate to tabulateVec)
open import Data.Vec.Relation.Unary.Any renaming (Any to AnyVec ; any to anyVec)
open import Data.Vec.Relation.Unary.All renaming (All to AllVec ; all to allVec)
open import Hash
open import Level using (0ℓ)

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

  -- _≟?R_ : ∀(r₁ r₂ : Record) → Dec (r₁ ≟?R r₂)
  -- (block _) ≟R (qc _) = no ?

  data HashOrRec : Set where
   horRec  : Record → HashOrRec
   horHash : Hash   → HashOrRec

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
  data _←_ : HashOrRec → HashOrRec → Set where
    q←b : ∀ {q : QC}{b : Block}
          → hashR (qc q) ≡ Block.prevQCHash b
          → horRec (qc q) ← horRec (block b)
    b←q : ∀ {q : QC}{b : Block}
          → hashR (block b) ≡ QC.blockHash q
          → horRec (block b) ← horRec (qc q)
    h←b : ∀ {b : Block}{h : QCHash}
          → Block.prevQCHash b ≡ h
          → horHash h ← horRec (block b)

  -- Definition of R₁ ←⋆ R₂
  data _←⋆_ : HashOrRec → HashOrRec → Set where
    ss0 : ∀ {s₁ s₂    : HashOrRec}
          → s₁ ← s₂
          → s₁ ←⋆ s₂
    ssr : ∀ {s₁ s₂ s₃ : HashOrRec}
          → s₁ ←⋆ s₂
          → s₂ ← s₃
          → s₁ ←⋆ s₃

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

  data isInRS {h} : Record → RecordStore h → Set where
    base : ∀ (s : RecordStore h)
           → (r : Record)
           → (v : Valid r s)
           → isInRS r (insert s r v)
    recu : ∀ (r r' : Record)
           → (s : RecordStore h)
           → (v : Valid r' s)
           → isInRS r s
           → isInRS r (insert s r' v)

  {- For now I am not including in the validation the Hash of the states
   - No constraint about no dup qc elements
   -}
  Valid {h} (block b) rs =
    h ≡ Block.prevQCHash b ⊎
    ∃[ q ] ( isInRS (qc q) rs
           × (hashR (qc q) ≡ Block.prevQCHash b)
           × QC.round q < Block.round b)

  Valid (qc q) empty                  = ⊥
  Valid (qc q) (insert rs r x)        =
    ∃[ b ] ( isInRS (block b) rs
           × hashR (block b) ≡ QC.blockHash q
           × QC.round q ≡ Block.round b
           × All (_≡_ (hashR (block b)))
                  (List-map (Vote.blockHash) (QC.votes q)) )

  -- Lemma S₁ ---------------------------------------------------

  hᵢ←⋆R : ∀ {hᵢ : HInit} {r : Record} {rs : RecordStore hᵢ}
          → isInRS r rs
          → horHash hᵢ ←⋆ horRec r
  hᵢ←⋆R {hᵢ} {block b} {empty} ()
  hᵢ←⋆R {hᵢ} {block b} {insert rs (block .b) v} (base .rs .(block b) .v)
   with v
  ...| inj₁ xx = ss0 (h←b (sym xx))
  ...| inj₂ vq
     with vq
  ...|   ⟨ q , ⟨ inrs , ⟨ h , _ ⟩ ⟩ ⟩
         = ssr {horHash hᵢ} {horRec (qc q)} (hᵢ←⋆R {hᵢ} {qc q} {rs} inrs) (q←b h)
  -- Agda shows a "catchall" highlighting here.  Not going to figure it out.
  -- Possibly related to: https://github.com/agda/agda/issues/2124
  hᵢ←⋆R {hᵢ} {block b} {insert rs _ _}          (recu .(block b) _ rs' _ irns)
        = hᵢ←⋆R {hᵢ} {block b} {rs'} irns

  hᵢ←⋆R {hᵢ} {qc q} {empty} ()
  hᵢ←⋆R {hᵢ}        {rs = insert empty (qc q) ()}
  hᵢ←⋆R {hᵢ} {qc q} {insert (insert rs r x₁) .(qc q) x₂} (base .(insert rs r x₁) .(qc q) x₂)
    with x₂
  ...| ⟨ b , ⟨ inrs , ⟨ h , xx ⟩ ⟩ ⟩
       = ssr {horHash hᵢ} {horRec (block b)} (hᵢ←⋆R {hᵢ} {block b} {rs} inrs) (b←q h)
  -- More catchall noise, see above
  hᵢ←⋆R {hᵢ} {qc q} {insert rs _ _}          (recu .(qc q) _ rs' _ irns)
        = hᵢ←⋆R {hᵢ} {qc q} {rs'} irns


--   ←inj : ∀ {r₀ r₁ r₂ : Record} → (hashR r₀ ← r₂) → (hashR r₁ ← r₂)
--            → r₀ ≡ r₁ ⊎ HashBroke
--   ←inj {r₀} {r₁} {block b} hr₀≡phb hr₁≡phb
--     with hash-cr (trans hr₀≡phb (sym hr₁≡phb))
--   ... | inj₁ ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ =
--              inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ ⟩
--   ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)

--   ←inj {r₀} {r₁} {qc q}    hr₀≡phb hr₁≡phb
--     with hash-cr (trans hr₀≡phb (sym hr₁≡phb))
--   ... | inj₁ ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ =
--              inj₂ ⟨ ⟨ (encodeR r₀) , (encodeR r₁) ⟩ , ⟨ er₀≢er₁ , hr₀≡hr₁ ⟩ ⟩
--   ... | inj₂ er₀≡er₁ = inj₁ (encodeR-inj er₀≡er₁)

--   round-mono : ∀  {hᵢ : HInit} {r₀ r₁ r₂ : Record} {rs : RecordStore hᵢ}
--                  → Valid r₀ rs → Valid r₁ rs → Valid r₂ rs
--                  → hashR r₀ ←⋆ r₂ × hashR r₁ ←⋆ r₂
--                  → round r₀ < round r₁
--                  → (hashR r₀ ←⋆ r₁) ⊎ HashBroke
--   round-mono = {!!}

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

-------------------- Properties of Authors  ---------------------

  open Author

  data _≡-Author_ : Relation.Binary.Rel Author 0ℓ where
    a₁≡a₂ : ∀{a₁ a₂} → id a₁ ≡ id a₂ → a₁ ≡-Author a₂

  ≢-Author-id : ∀ {m n}
              → (a₁ a₂ : Author)
              → id a₁ ≡ m
              → id a₂ ≡ n
              → m ≢ n
              → Relation.Nullary.¬ (a₁ ≡-Author a₂)
  ≢-Author-id {m} {n} a₁ a₂ id₁ id₂ m≢n prf
    with prf
  ...| a₁≡a₂ idprf = m≢n (trans (sym id₁) (trans idprf id₂))

  _≟-Author_ : (a₁ : Author) → (a₂ : Author) → Dec (a₁ ≡-Author a₂)
  a₁ ≟-Author a₂ with id a₁ ≟ id a₂
  ...| yes xx =  yes (a₁≡a₂ xx)
  ...| no  xx =  no  (≢-Author-id a₁ a₂ refl refl xx)

  _≡-Author?_ : (a₁ : Author) → (a₂ : Author) → Bool
  a₁ ≡-Author? a₂ with a₁ ≟-Author a₂
  ...| yes _ = true
  ...| no  _ = false

---------------------- Epoch Configuration  ---------------------

  data DistinctVec {ℓ} {A} (_P_ : A → A → Set ℓ) : ∀ {n} → (Vec {ℓ} A n) → Set (Level.suc ℓ) where
    distinct : ∀ {n} (v : Vec A n)
             → AllVec (λ i → (AllVec (λ j → i ≡ j ⊎ (lookupVec v i) P (lookupVec v j)) (allFinVec n))) (allFinVec n)
             → DistinctVec _P_ v

  record EpochConfiguration : Set (Level.suc Level.zero) where
    field
      f : ℕ                          -- Maxiumum number of faulty nodes in this epoch
      n : ℕ                          -- Total number of nodes who can vote in this epoch
      3f<n : 3 * f < n               -- Require n > 3 * f
      votingRights : Vec Author n    -- For now we consider all "active" authors have equal voting rights
      votersDistinct : DistinctVec {Level.zero} {Author} _≡-Author_ {n} votingRights 
      goodGuys : Vec (Fin n) (n ∸ f) -- OK to model exactly f bad guys; if fewer, it's as if some bad guys
                                     -- behave exactly like good guys.  To ensure goodGuys are in votingRights,
                                     -- we model them by index into votingRights, rather than as Authors

  open EpochConfiguration

  -- Test data

  dummyAuthor : ℕ → Author
  dummyAuthor i = record {id = i ; privKey = dummyByteString}

  dummyAuthors : (n : ℕ) → Vec Author n
  dummyAuthors n = tabulateVec (dummyAuthor ∘ Data.Fin.toℕ)

  dummyAuthorsDistinct : ∀ (n : ℕ) → DistinctVec {Level.zero} _≡-Author_ (dummyAuthors n)
  dummyAuthorsDistinct n = {!!}
  -- with allVec ... ?
  -- distinct (dummyAuthors n) {!!}

  _ : Data.Vec.lookup (dummyAuthors 4) (Data.Fin.fromℕ≤ {3} (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ dummyAuthor 3
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors 4) (Data.Fin.fromℕ≤ {2} (s≤s (s≤s (s≤s z≤n))))       ≡ dummyAuthor 2
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors 4) (Data.Fin.fromℕ≤ {1} (s≤s (s≤s z≤n)))             ≡ dummyAuthor 1
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors 4) (Data.Fin.fromℕ≤ {0} (s≤s z≤n))                   ≡ dummyAuthor 0
  _ = refl

  dummyGoodGuys : (take : ℕ) → (drop : ℕ) → Vec (Fin (take + drop)) take
  dummyGoodGuys take drop = takeVec take {drop} (allFinVec (take + drop))

  3<4 : 3 < 4
  3<4 = s≤s (s≤s (s≤s (s≤s z≤n)))

  ec1 : EpochConfiguration
  ec1 = record {
          f = 1
        ; n = 4
        ; 3f<n = 3<4
        ; votingRights = dummyAuthors 4
        ; votersDistinct = dummyAuthorsDistinct 4
        ; goodGuys     = dummyGoodGuys 3 1
        }

  ------------------------- End test data ----------------------

  isVoter? : (ec : EpochConfiguration)
           → (a : Author)
           → Dec (AnyVec (a ≡-Author_) (votingRights ec))
  isVoter? ec a = anyVec (a ≟-Author_) {n ec} (votingRights ec)

  isVoter : (ec : EpochConfiguration) → (a : Author) → Bool
  isVoter ec a with
    isVoter? ec a
  ...| yes _ = true
  ...| no  _ = false

  _ : isVoter ec1 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isVoter ec1 (dummyAuthor 5) ≡ false
  _ = refl

  isHonest? : (ec : EpochConfiguration)
            → (a  : Author)
            → Dec (AnyVec (λ i → a ≡-Author lookupVec (votingRights ec) i) (goodGuys ec))
  isHonest? ec a = anyVec (λ i → a ≟-Author (lookupVec (votingRights ec) i)) {n ec ∸ f ec} (goodGuys ec)

  isHonestP : (ec : EpochConfiguration)
            → (a  : Author)
            → Bool
  isHonestP ec a with isHonest? ec a
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
