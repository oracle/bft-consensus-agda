open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (Decidable)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_])
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
open import Data.Fin.Properties using (toℕ-injective) renaming (_≟_ to _≟Fin_)
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

---------------------- Epoch Configuration  ---------------------

  -- TODO: Move to more generic location
  data DistinctVec {ℓ} {A} (_P_ : A → A → Set ℓ) {n} (v : Vec {ℓ} A n) : Set (Level.suc ℓ) where
    distinct : (∀ (i j : Fin n) → i ≡ j ⊎ (¬ (lookupVec v i) P (lookupVec v j)))
             → DistinctVec _P_ v

  record EpochConfiguration : Set (Level.suc Level.zero) where
    field
      ecN : ℕ                               -- Total number of nodes who can vote in this epoch
      ecF : ℕ                               -- Maxiumum number of faulty nodes in this epoch
      ecVotingRights : Vec Author ecN
      -- Required properties for parameters and votingRights
      ecAux0<n  : 0 < ecN
      ecAux3f<n : 3 * ecF < ecN                    -- Require n > 3 * f
      ecAuxVotersDistinct : DistinctVec _≡_ ecVotingRights
                                                   -- For now we consider all "active" authors have equal voting rights
      ecAuxGoodGuys : Vec (Fin ecN) (ecN ∸ ecF)    -- OK to model exactly f bad guys; if fewer, it's as if some bad guys
                                                   -- behave exactly like good guys.  To ensure goodGuys are in votingRights,
                                                   -- we model them by index into votingRights, rather than as Authors
      ecAuxGoodGuysDistinct : DistinctVec _≡_ ecAuxGoodGuys

  open EpochConfiguration

  isVoter? : (ec : EpochConfiguration)
           → (a : Author)
           → Dec (AnyVec (a ≡_) (ecVotingRights ec))
  isVoter? ec a = anyVec (a ≟_) {ecN ec} (ecVotingRights ec)

  isVoter : (ec : EpochConfiguration) → (a : Author) → Bool
  isVoter ec a with isVoter? ec a
  ...| no  _ = false
  ...| yes _ = true

------------------------- Begin test data ----------------------

  testF = 1

  testN = 4
  0<testN : 0 < testN
  0<testN = s≤s z≤n

  3*testF<testN : (3 * testF) < testN
  3*testF<testN = s≤s (s≤s (s≤s (s≤s z≤n)))

-------------------- Properties of Authors  ---------------------

  dummyAuthor : ℕ → Author
  dummyAuthor i = i

  dummyAuthors : ∀ n → Vec Author n
  dummyAuthors  n = tabulateVec (dummyAuthor ∘ toℕ)

------------------------- Begin tests ----------------------

  _ : Data.Vec.lookup (dummyAuthors testN) (Data.Fin.fromℕ≤ {3} (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ dummyAuthor 3
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN) (Data.Fin.fromℕ≤ {2} (s≤s (s≤s (s≤s z≤n))))       ≡ dummyAuthor 2
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN) (Data.Fin.fromℕ≤ {1} (s≤s (s≤s z≤n)))             ≡ dummyAuthor 1
  _ = refl

  _ : Data.Vec.lookup (dummyAuthors testN) (Data.Fin.fromℕ≤ {0} (s≤s z≤n))                   ≡ dummyAuthor 0
  _ = refl

------------------------- End tests ----------------------

  dummyAuthorsBijective : ∀ {n} → {i : Fin n} → lookupVec (dummyAuthors n) i ≡ dummyAuthor (toℕ i)
  dummyAuthorsBijective {n} {i} rewrite (lookup∘tabulate {n = n} toℕ) i = refl

  dummyAuthorsDistinct′ : ∀ {n}
                          → 0 < n
                          → {i j : Fin n}
                          → i ≡ j ⊎ ¬ lookupVec (dummyAuthors n) i ≡ lookupVec (dummyAuthors n) j
  dummyAuthorsDistinct′ {n} 0<n {i} {j}
     with toℕ i ≟ toℕ j
  ...| yes xxx = inj₁ (toℕ-injective xxx)
  ...| no  xxx rewrite dummyAuthorsBijective {n} {i}
                     | dummyAuthorsBijective {n} {j} = inj₂ xxx

  dummyAuthorsDistinct : ∀ {n} → DistinctVec {Level.zero} _≡_ (dummyAuthors n)
  dummyAuthorsDistinct {0}     = distinct λ ()
  dummyAuthorsDistinct {suc n} = distinct (λ i j → dummyAuthorsDistinct′ {suc n} (s≤s z≤n) {i} {j})

  --- Good guys

  -- TODO: move to lemmas
  finsuc-injective : ∀ {n : ℕ} {i j : Fin n} → Fin.suc i ≡ Fin.suc j → i ≡ j
  finsuc-injective {n} {i} {.i} refl = refl

  upgrade : ∀ {take drop} → Fin take → Fin (take + drop)
  upgrade {take} {drop} x = Data.Fin.inject≤ {take} {take + drop} x (m≤m+n take drop)

  upgrade-injective : ∀ {take drop} {i j}
                      → upgrade {take} {drop} i ≡ upgrade {take} {drop} j
                      → i ≡ j
  upgrade-injective {i = Data.Fin.0F} {j = Data.Fin.0F} ui≡uj = refl
  upgrade-injective {i = Fin.suc i}   {j = Fin.suc j}   ui≡uj
    with i ≟Fin j
  ... | yes p = cong Fin.suc p
  ... | no ¬p = let i≡j = upgrade-injective (finsuc-injective ui≡uj)
                in contradiction i≡j ¬p

  dummyGoodGuys : (take : ℕ) → (drop : ℕ) → Vec (Fin (take + drop)) take
  dummyGoodGuys take drop = tabulateVec {n = take} (upgrade {take} {drop})

  dummyGoodGuysBijective : ∀ n-f f
                         → 0 < n-f
                         → {i : Fin n-f}
                         → lookupVec (dummyGoodGuys n-f f) i ≡ upgrade {n-f} {f} i
  dummyGoodGuysBijective n-f f 0<f {i} = lookup∘tabulate {n = n-f} (upgrade {n-f} {f}) i 

  dummyGoodGuysDistinct′ : ∀ {n-f f : ℕ}
                          → 0 < n-f
                          → {i j : Fin n-f}
                          → i ≡ j ⊎ ¬ lookupVec (dummyGoodGuys n-f f) i ≡ lookupVec (dummyGoodGuys n-f f) j
  dummyGoodGuysDistinct′ {n-f} {f} 0<n-f {i} {j}
     with i ≟Fin j
  ...| yes xxx = inj₁ xxx
  ...| no  xxx rewrite dummyGoodGuysBijective n-f f 0<n-f {i}
                     | dummyGoodGuysBijective n-f f 0<n-f {j} = inj₂ λ x → xxx (upgrade-injective {n-f} {f} {i} {j} x)

  dummyGoodGuysDistinct : ∀ {n-f} {f} → DistinctVec {Level.zero} _≡_ (dummyGoodGuys n-f f)
  dummyGoodGuysDistinct {0}     = distinct λ ()
  dummyGoodGuysDistinct {suc n-f} = distinct (λ i j → dummyGoodGuysDistinct′ {suc n-f} (s≤s z≤n) {i} {j})

  ec1 : EpochConfiguration
  ec1 = record {
          ecN                   = testN
        ; ecF                   = testF
        ; ecVotingRights        = dummyAuthors testN
        ; ecAux0<n              = 0<testN
        ; ecAux3f<n             = 3*testF<testN
        ; ecAuxVotersDistinct   = dummyAuthorsDistinct
        ; ecAuxGoodGuys         = dummyGoodGuys (testN ∸ testF) testF
        ; ecAuxGoodGuysDistinct = dummyGoodGuysDistinct
        }

  _ : lookupVec (ecVotingRights ec1) (Data.Fin.fromℕ≤ (s≤s z≤n))                   ≡ dummyAuthor 0
  _ = refl

  _ : lookupVec (ecVotingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s z≤n)))             ≡ dummyAuthor 1
  _ = refl

  _ : lookupVec (ecVotingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s z≤n))))       ≡ dummyAuthor 2
  _ = refl

  _ : lookupVec (ecVotingRights ec1) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ dummyAuthor 3
  _ = refl

  _ : isVoter ec1 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isVoter ec1 (dummyAuthor 3) ≡ true
  _ = refl

  _ : isVoter ec1 (dummyAuthor 5) ≡ false
  _ = refl

------------------------- End test data ----------------------

  goodGuyIsAuthor : (ec : EpochConfiguration) → (a : Author) → (x  : Fin (ecN ec)) → Set
  goodGuyIsAuthor ec a x = a ≡ lookupVec (ecVotingRights ec) x

  goodGuyIsAuthor? : (ec : EpochConfiguration) → (a : Author) → (x  : Fin (ecN ec)) → Dec (goodGuyIsAuthor ec a x)
  goodGuyIsAuthor? ec a  x = a ≟ lookupVec (ecVotingRights ec) x

  isHonestP : (ec : EpochConfiguration)
            → (a  : Author)
            → Set
  isHonestP ec a = AnyVec (goodGuyIsAuthor ec a) (ecAuxGoodGuys ec)

  isHonest? : (ec : EpochConfiguration)
            → (a  : Author)
            → Dec (isHonestP ec a)
  isHonest? ec a = anyVec (goodGuyIsAuthor? ec a) {ecN ec ∸ ecF ec} (ecAuxGoodGuys ec)

  isHonest : (ec : EpochConfiguration)
           → (a  : Author)
           → Bool
  isHonest ec a with isHonest? ec a
  ...| yes _ = true
  ...| no  _ = false

  _ : isHonest ec1 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isHonest ec1 (dummyAuthor 1) ≡ true
  _ = refl

  _ : isHonest ec1 (dummyAuthor 2) ≡ true
  _ = refl

  _ : isHonest ec1 (dummyAuthor 3) ≡ false
  _ = refl

  _ : isHonest ec1 (dummyAuthor 5) ≡ false
  _ = refl

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
      epochId   : EpochId
      round     : Round
      blockHash : BlockHash
      -- state     : State
      author    : Author
      --signature : Signature

 -- QuorumCertificate ------------------------------
  record QC : Set where
  -- TODO: record QC (ec : EpochConfiguration) : Set where
    field
      -- epoch     : EpochId
      blockHash : BlockHash
      round     : Round
      -- state     : State
      votes     : List Vote
      author    : Author

  record Initial : Set where
    constructor mkInitial
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
  -- TODO: data Record (ec : EpochConfiguration) : Set where
    B : Block   → Record
    Q : QC      → Record
    V : Vote    → Record
    T : Timeout → Record

  data isChainableRecord : Record → Set where
    B : ∀ (b : Block) → isChainableRecord (B b)
    Q : ∀ (q : QC)    → isChainableRecord (Q q)
    V : ∀ (v : Vote)  → isChainableRecord (V v)

  data _∈Rec_ : Record → Record → Set where
    V∈V  : ∀ (v₁ v₂ : Vote) → v₁ ≡ v₂ → (V v₁) ∈Rec (V v₂)
    -- V∈QC : ∀ (v : Vote) (q : QC) →  TODO: ... Data.List.Any

  open Initial

  -- This seems silly, there should be a more generic way
  -- Also, after figuring this out, I figured out I didn't
  -- need it, at least for the reason I thought I needed it.
  -- Leaving it here in case someone helps me learn how not
  -- to waste time on this in future!
  ≡-Initial : ∀ {e₁ e₂ : EpochId} {s₁ s₂ : ℕ}
            → e₁ ≡ e₂
            → s₁ ≡ s₂
            → mkInitial e₁ s₁ ≡ mkInitial e₂ s₂
  ≡-Initial refl refl = refl

  _≟Initial_ : (i₁ i₂ : Initial) → Dec (i₁ ≡ i₂)
  i₁ ≟Initial i₂
     with epochId i₁ ≟ epochId i₂
  ...| no  xx = no (xx ∘ (cong epochId))
  ...| yes xx
       with seed i₁ ≟ seed i₂
  ...|   yes xx1 = yes (≡-Initial xx xx1)
  ...|   no  xx1 = no (xx1 ∘ (cong seed))

  round : Record → Round
  round (B b) = Block.round b
  round (Q q) = QC.round q
  round (V v) = Vote.round v
  round (T t) = Timeout.toRound t

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
  data _←_ : RecOrInit → Record → Set where
    I←B : ∀ {i : Initial} {b : Block}
          → HashR (I i) ≡  Block.prevQCHash b
          → I i ← B b
    Q←B : ∀ {q : QC} {b : Block}
          → HashR (R (Q q)) ≡  Block.prevQCHash b
          → R (Q q) ← B b
    B←Q : ∀ {b : Block} {q : QC}
          → HashR (R (B b)) ≡ QC.blockHash q
          → R (B b) ← Q q

  data _←⋆_ (r₁ : RecOrInit) (r₂ : Record) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : Record} → (r₁ ←⋆ r) → (R r ← r₂) → r₁ ←⋆ r₂

------------------------- RecordStore --------------------------

  data RecordStore (sᵢ : Initial) : Set

  data Valid : {sᵢ : Initial} → Record → RecordStore sᵢ → Set

  data RecordStore sᵢ where
    empty  : RecordStore sᵢ
    insert : {r : Record} (s : RecordStore sᵢ)
             → Valid r s → RecordStore sᵢ

  data _∈Rs_ {sᵢ} (r : Record) : RecordStore sᵢ → Set where
    here  : ∀ (s : RecordStore sᵢ) (v : Valid r s) → r ∈Rs insert s v
    there : ∀ (r' : Record) (s : RecordStore sᵢ) (v : Valid r' s)
           → r ∈Rs s
           → r ∈Rs (insert s v)

  _dependsOnBlock_wrt_   : ∀ {sᵢ} Record → Block → RecordStore sᵢ → Set
  r dependsOnBlock b wrt rs = Valid (B b) rs × R (B b) ← r × round (B b) ≡ round r

  _dependsOnQC_wrt_      : ∀ {sᵢ} Record → QC → RecordStore sᵢ → Set
  r dependsOnQC q wrt rs = Valid (Q q) rs × R (Q q) ← r × round (Q q) < round r

  _dependsOnInitial_  : Record → Initial → Set
  r dependsOnInitial i = (I i) ← r × 1 ≤ round r

  -- Conditions required to add a Record to a RecordStore (which contained "previously verified"
  -- records, in the parlance of the LibraBFT paper.  Some properties do not depend on any
  -- particular RecordStore and their proofs can ignore the RecordStore, other than passing it to
  -- recursive invocations.
  data Valid where
    B : ∀ {sᵢ} (b : Block)   (rs : RecordStore sᵢ) → (∃[ q ] ((Q q) ∈Rs rs × (B b) dependsOnQC q wrt rs)) ⊎ (B b) dependsOnInitial sᵢ → Valid (B b) rs
    Q : ∀ {sᵢ} (q : QC)      (rs : RecordStore sᵢ) → (∃[ b ] ((B b) ∈Rs rs × (Q q) dependsOnBlock b wrt rs))                          → Valid (Q q) rs
    V : ∀ {sᵢ} (v : Vote)    (rs : RecordStore sᵢ) → (∃[ b ] ((B b) ∈Rs rs × (V v) dependsOnBlock b wrt rs))                          → Valid (V v) rs
    T : ∀ {sᵢ} (t : Timeout) (rs : RecordStore sᵢ)                                                                                      → Valid (T t) rs

  {-- Needs to come after EpochConfiguration definition
  -- TODO: A valid quorum certificate for an EpochConfiguration ec should consist of:
  --  at least (ecN ∸ ecF) pairs (a,s)
  --  the a's should be distinct (I don't think the paper says thus, but it's obviously needed)
  --  for each pair (a,s), the following should hold:
  --    isVoter ec a
  --    s should be a signature by a on a vote constructed using the fields of the quorum certificate up
  --      to and including commitment
  validQC : EpochConfiguration → QC → Set
  validQC ec q = {!!}
  --}

-- Lemma S₁ ---------------------------------------------------

  -- Note: part 1 of Lemma S1 comes later, as it depends on RecordStoreState because of the
  -- "previously verified" requirement in Section 4.2

  -- 2
  ←inj : ∀ {r₀ : RecOrInit}{r₁ r₂ : Record} → (r₀ ← r₂) → (R r₁ ← r₂)
           → r₀ ≡ R r₁ ⊎ HashBroke
  ←inj {i} {q} {b} (I←B i←b) (Q←B q←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ ⟨ i≢q , hi≡hq ⟩
             = inj₂ ⟨ ⟨ encodeR i , encodeR (R q) ⟩ , ⟨ i≢q , hi≡hq ⟩ ⟩
  ... | inj₂ i≡q
             = contradiction (encodeR-inj i≡q) λ ()

  ←inj {q₀} {q₁} {b} (Q←B q₀←b) (Q←B q₁←b)
    with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩
             = inj₂ ⟨ ⟨ encodeR q₀ , encodeR (R q₁) ⟩ , ⟨ q₀≢q₁ , hq₀≡hq₁ ⟩ ⟩
  ... | inj₂ q₁≡q₂
             = inj₁ (encodeR-inj q₁≡q₂)

  ←inj {b₀} {b₁} {q} (B←Q b₀←q) (B←Q b₁←q)
    with hash-cr (trans b₀←q (sym b₁←q))
  ... | inj₁ ⟨ b₀≢b₁ , hb₀←hb₁ ⟩
             = inj₂ ⟨ ⟨ encodeR b₀ , encodeR (R b₁) ⟩ , ⟨ b₀≢b₁ , hb₀←hb₁ ⟩ ⟩
  ... | inj₂ b₀≡b₁
             = inj₁ (encodeR-inj b₀≡b₁)

  -- 3

  -- Aux Lemma
  -- This property does not depend on any particular RecordStore, and referring
  -- to it will unnecessarily complicate proofs.  The parameters is needed for
  -- recursive invocations of Valid, so it it provided but named "doNotUse" as
  -- a reminder.
  r₀←⋆r₁→rr₀≤rr₁ : {sᵢ : Initial} {r₀ r₁ : Record}{doNotUse : RecordStore sᵢ} 
                 → R r₀ ←⋆ r₁
                 → Valid {sᵢ} r₁ doNotUse
                 → HashBroke ⊎ round r₀ ≤ round r₁
  r₀←⋆r₁→rr₀≤rr₁ {r₁ = B b} (ss0 (Q←B x)) v₁
     with v₁
  ...| B blk _ prf
       with prf
  ...|   inj₁ xx = {!!}  -- Block b depends directly on QC
  ...|   inj₂ xx = {!!}  -- Block b depends directly on Initial

  r₀←⋆r₁→rr₀≤rr₁ {r₁ = Q q} (ss0 r₀←r₁) v₁
       with v₁
  ...| Q qc _ prf
       with prf
  ...|   dob = {!!}      -- QC q depends directly on Block

  r₀←⋆r₁→rr₀≤rr₁ {sᵢ} {r₁ = B b} (ssr {r} r₀←⋆r r←r₁) (B b rs (inj₁ doqc)) = {!!}
  r₀←⋆r₁→rr₀≤rr₁ {sᵢ} {r₁ = B b} (ssr {r} r₀←⋆r r←r₁) (B b rs (inj₂ doi))  = {!!}

  r₀←⋆r₁→rr₀≤rr₁      {r₁ = Q q} (ssr r₀←⋆r r←r₁) v₁ = {!!}

  -- Lemma 1, part 3
  -- This property does not depend on any particular RecordStore, and referring
  -- to it will unnecessarily complicate proofs.  The parameters is needed for
  -- recursive invocations of Valid, so it it provided but named "doNotUse" as
  -- a reminder.
  round-mono : ∀  {sᵢ : Initial} {r₀ r₁ r₂ : Record} {doNotUse : RecordStore sᵢ}
                 → R r₀ ←⋆ r₂
                 → R r₁ ←⋆ r₂
                 → Valid {sᵢ} r₀ doNotUse
                 → Valid {sᵢ} r₁ doNotUse
                 → Valid {sᵢ} r₂ doNotUse
                 → round r₀ < round r₁
                 → (R r₀ ←⋆ r₁) ⊎ HashBroke
  round-mono (ssr r₀←⋆r r←r₂) (ssr r₁←⋆r′ r′←r₂) v₀ v₁ v₂ rr₀<rr₁
     with r←r₂ | r′←r₂
  ...| B←Q xx1 | B←Q xx2 = {!!}
  ...| Q←B xx1 | Q←B xx2 = {!!}

  round-mono (ss0 r₀←r₂)      (ssr r₁←⋆r′ r′←r₂) v₀ v₁ v₂ rr₀<rr₁ = {!!}

  round-mono (ssr r₀←⋆r r←r₂) (ss0 r₁←r₂)         v₀ v₁ v₂ rr₀<rr₁ = {!!}

  round-mono (ss0 r₀←r₂)      (ss0 r₁←r₂)         v₀ v₁ v₂ rr₀<rr₁ = {!!}

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

  open RecordStoreState

-------------------- Lemma S1, part 1 --------------------

  hᵢ←⋆R : ∀ {sᵢ : Initial} {r : Record} {isCR : isChainableRecord r} {s : RecordStore sᵢ}
          → r ∈Rs s
          → (I sᵢ) ←⋆ r

  hᵢ←⋆R {isCR = isCR} (there _ s _ r∈s) = hᵢ←⋆R {isCR = isCR} r∈s
  hᵢ←⋆R {r = B b} (here rs vB)
    with vB
  ...| B {sᵢ} .b rs (inj₂ ⟨ doi , _ ⟩) = ss0 doi
  ...| B {sᵢ} .b rs (inj₁ ⟨ qc , (q∈rs , bDOq )⟩) =
       ssr (((hᵢ←⋆R {sᵢ} {Q qc} {Q qc} {rs} q∈rs))) (proj₁ (proj₂ bDOq) )

  hᵢ←⋆R {r = Q q} (here rs vQ)
     with vQ
  ...| Q {sᵢ} .q rs ⟨ b , (b∈rs , qDOb) ⟩ =
       ssr (hᵢ←⋆R {sᵢ} {B b} {B b} {rs} b∈rs) (proj₁ (proj₂ qDOb))

  hᵢ←⋆R {r = V v} (here rs vV)
     with vV
  ...| V {sᵢ} .v rs ⟨ b , (b∈rs , vDOb) ⟩ =
       ssr (hᵢ←⋆R {sᵢ} {B b} {B b} {rs} b∈rs) (proj₁ (proj₂ vDOb))

  lemma1-1 : RecordStoreState → Set
  lemma1-1 rss = ∀ {r : Record} {isCR : isChainableRecord r}
               → r ∈Rs recStore rss
               → (I (sᵢ rss)) ←⋆ r

  record AuxRecordStoreState : Set where
    field
      auxRssData     : RecordStoreState
      auxRssLemma1-1 : lemma1-1 auxRssData

-------------------- RecordStoreState tests --------------------

  rss1 : RecordStoreState
  rss1 = record {
             epoch     = 1
           ; sᵢ        = record { epochId = 1 ; seed = 1 }
           ; recStore  = empty
           ; curRound  = 1
           ; highQCR   = 1 -- should this be a Maybe?
           ; listVotes = []
         }

  arss1 : AuxRecordStoreState
  arss1 = record {
              auxRssData = rss1
            ; auxRssLemma1-1 = λ {r} x → contradiction x (λ ())
          }

  testInit : Initial
  testInit = record { epochId = 1
                    ; seed    = 1
                    }

  block1 : Block
  block1 = record { round = 1
                  ; prevQCHash = HashR (I testInit)
                  ; author = dummyAuthor 0
                  }

  rss2 : RecordStoreState
  rss2 = record rss1 { recStore = insert {sᵢ rss1} {B block1}
                                         (recStore rss1)
                                         (B {sᵢ rss1} block1 empty (inj₂ ⟨ I←B {sᵢ rss1} {block1} refl , s≤s z≤n ⟩))}

  arss2 : AuxRecordStoreState
  arss2 = record {
              auxRssData = rss2
            ; auxRssLemma1-1 = λ {r} {isCR} x → hᵢ←⋆R {r = r} {isCR = isCR} x
          }

  -- TODO : Add tests showing we can also add Blocks that depend on QCs, and we can add QCs and
  -- Votes and still preserve lemma 1-1

-------------------------- BFT assumption -----------------------

  -- TODO: We should be able to prove this for any EpochConfiguration because it follows from the
  -- constraints on that type (we have exactly N - F) "good guys", which are distinct and are
  -- indexes into votingRights (authors), which are also distinct.  But it is not clear if this
  -- is in a useful form to use in proofs, so not bothering to prove it now.  When we work on Lemma
  -- S2, we will need to use this assumption, so we can see then whether this is a useful way to
  -- state the assumption.  I think we will generally use BFTQuorumIntersection (below), so perhaps
  -- this definition is not needed.

  BFTAssumption : (ec : EpochConfiguration)
    → Data.Vec.Bounded.Vec≤.length
        (filterVec {P = isHonestP ec} (isHonest? ec) (Data.Vec.Bounded.fromVec (ecVotingRights ec)))
      ≡ (ecN ec) ∸ (ecF ec)
  BFTAssumption = {!!}

  -- TODO: move near other validity conditions, which will need to depend on EpochConfiguration
  --       See commented out definition and notes above
  validQC : EpochConfiguration → QC → Set
  validQC ec q = {!!}

  -- Define a notion of an author being "in" a quorum certificate for a given EpochConfiguration
  _∈Qs_for_ : Author → QC → EpochConfiguration → Set
  a ∈Qs q for ec = {!!}

  -- Should be provable from constraints on EpochConfigurations
  BFTQuorumIntersection : (ec : EpochConfiguration)
                        → (q₁ q₂ : QC)
                        → validQC ec q₁
                        → validQC ec q₂
                        → ∃[ a ] ( a ∈Qs q₁ for ec × a ∈Qs q₂ for ec × isHonestP ec a)
  BFTQuorumIntersection = {!!}


  {-- Needs to come after EpochConfiguration definition
  -- TODO: A valid quorum certificate for an EpochConfiguration ec should consist of:
  --  at least (ecN ∸ ecF) pairs (a,s)
  --  the a's should be distinct (I don't think the paper says thus, but it's obviously needed)
  --  for each pair (a,s), the following should hold:
  --    isVoter ec a
  --    s should be a signature by a on a vote constructed using the fields of the quorum certificate up
  --      to and including commitment
  validQC : EpochConfiguration → QC → Set
  validQC ec q = {!!}
  --}

---------------- Message types ----------------

  record DataSyncNotification : Set where
    field
      -- Current epoch identifier.
      dsnCurrentEpoch : EpochId
      -- Tail QC of the highest commit rule.
      dsnHighestCommitCertificate : Maybe QC
      -- Highest QC.
      dsnHighestQuorumCertificate : Maybe QC
      -- Timeouts in the highest TC, then at the current round, if any.
      dsnTimeouts : List Timeout
      -- Sender's vote at the current round, if any (meant for the proposer).
      dsnCurrentVote : Maybe Vote
      -- Known proposed block at the current round, if any.
      dsnProposedBlock : Maybe Block
      -- Active round of the sender's pacemaker.
      dsnActiveRound : Round

  record DataSyncRequest : Set where
    field
      -- Current epoch identifier.
      dsreqCurrentEpoch : EpochId
      -- Selection of rounds for which the receiver already knows a QC.
      dsreqKnownQuorumCertificates : List Round

  record EpochRecords : Set where
    field
      erEpochId : EpochId
      erRecords : List Record -- Could constrain them to be for the epoch, but should we?

  record DataSyncResponse : Set where
    field
      -- Current epoch identifier
      dsrspCurrentEpoch : EpochId
      -- Records for the receiver to insert, for each epoch, in the given order.
      dsrspRecords : List EpochRecords
      -- Active round of the sender's pacemaker.
      dsrspActiveRound : Round

  data Message : (s r : Author) → Set where
    DSN   : ∀ (s r : Author) → DataSyncNotification → Message s r
    DSREQ : ∀ (s r : Author) → DataSyncRequest      → Message s r
    DSRSP : ∀ (s r : Author) → DataSyncResponse     → Message s r

  data _∈msg_ : {s r : Author} → Record → Message s r → Set where
    -- DSRSP : ∀ {v : Vote} → {m : Message.DSRSP _ _ dsr} → (V v) ∈Rec TODO see if (V v) is in dsrspRecords .... → (V v) ∈msg m
    -- DSN   : ∀ {v : Vote} → {m : Message.DSN   _ _ dsn} → (V v) ∈Rec TODO see if (V v) is in dsnHighestCommitCertificate,  (perhaps not necessary since we have quorum)
    --                                                                                         dsnHighestQuorumCertificate,  (perhaps not necessary since we have quorum)
    --                                                                                         dsnCurrentEpoch
    --                                                                                         .... → (V c) ∈msg m




-------------------------- NodeState ---------------------------

  NodeTime : Set
  NodeTime = ℕ

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
      lockRound : Round
      -- latestVotedRound : Round
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

---------------------- Libra BFT Algorithm components ---------------

  proposeBlock : NodeState → Author → QCHash → NodeTime → SmrContext → Block × BlockHash
  proposeBlock = {!!}

  proposeBlockCond : NodeState
                   → Maybe QCHash
                   → SmrContext
                   → NodeState × SmrContext
  proposeBlockCond ns nothing smr = ns , smr
  proposeBlockCond ns (just qch) smr =
    let (blk , blkHash) = proposeBlock
                            ns
                            (NodeState.author ns)
                            qch
                            (nsLatestBroadcast ns)
                            smr
    in record ns { nsRecordStore     = {!!}
                 ; nsLatestBroadcast = {!!}    -- TODO: this is just random crap while experimenting
                 }
       , {!!}

  createTimeout' : ∀ {h} → RecordStore h → Author → Round → SmrContext → RecordStore h
  createTimeout' rs _ r _ = insert rs {! !} -- Can't prove valid to insert timeout until definitions fleshed out

  createTimeout : RecordStoreState → Author → Round → SmrContext → RecordStoreState
  createTimeout rss a r smr =
    record rss { recStore = createTimeout' {RecordStoreState.sᵢ rss} (RecordStoreState.recStore rss) a r smr }

  createTimeoutCond : NodeState → Maybe Round → SmrContext → NodeState
  createTimeoutCond ns nothing  _   = ns
                                                                      -- TODO: after merging with Lisandra, naming conventions
  createTimeoutCond ns (just r) smr = record ns { nsRecordStore = createTimeout (NodeState.nsRecordStore ns) (author ns) r smr }

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
      round = puaShouldCreateTimeout pacemakerActions
      self₁ = createTimeoutCond self₀ round smrContext₀

  -- if let Some(previous_qc_hash) = pacemaker_actions.should_propose_block {
  --   self.record_store.propose_block(
  --       self.local_author,
  --       previous_qc_hash,
  --       self.latest_broadcast,
  --       smr_context,
  --   );
      previousQCHashMB = puaShouldProposeBlock pacemakerActions
      -- TODO: we may need to modify the SMR context inside proposeBlock.  It's going to get
      -- painful here, as we will need to update both self amd SMR Context, based on the same
      -- condition
      (self₂ , smrContext₁) = proposeBlockCond self₁ previousQCHashMB smrContext₀



  -- }
  -- actions
  -- } }

    in {!!}

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

----------------------------- updateNode ------------------------

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
         pms₀ = nsPaceMaker self₀
         (pms₁ , pmActs ) = updatePacemaker pms₀
                                            (nsLocalAuthor self₀)
                                            (recStore (nsRecordStore self₀))
                                            (nsLatestBroadcast self₀)
                                            latestSenders
                                            clock

-- let mut actions = self.process_pacemaker_actions(pacemaker_actions, smr_context);
         -- Can't keep this organized as in paper, because can't do with & where here
         (self₁ , actions₀) = processPacemakerActions self₀ pmActs smrContext₀

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

---------------- Global system state -------------

{-
  - Authors (nodes, verifiers, consensus participants, whatever you want to call them)
  - Clients (they invoke commands and get responses; no need to model these in initially)

  - System state
    - For each author
      - NodeState
      - SmrContext (how many?  One per branch in RecordStore? One per block?)
    - Systemwide
      - Communication
        - Channels?  No, too detailed and specific
        - Need to think about assumptions on ordering, duplication, dropping, mutating

        - My first thought is that we should model reordring, duplication and dropping, but not
          mutating (messages are signed).  I also think we should consider point-to-point messages
          that have a source and destination (e.g., one author to another).  Therefore, we can model
          our communication system as a collection of indexes sets of messages.  Messages_i_j is
          that set of all messages ever sent from i to j.

        - Author a₁ "sending" a message will be adding an element Messages a₁ aᵢ for some aᵢ.

        - Author a₁ "receiving" a message will be possible for any element in Messages aᵢ a₁ for any
          aᵢ.

        - In this context, we would prove an invariant for the increasing round rules that says
          something like:

            honestVotes : ∀ {sc : SystemConfiguration}
                          → {ec : EpochConfiguration} {a : Author} {b : Block}
                          → {v₁ v₂ : Vote}
                          → ∃[ r ](v₁ ∈-msgs (messages sc) a r)
                          → ∃[ r ](v₂ ∈-msgs (messages sc) a r)
                          → Vote.round v₁ ≡ Vote.round v₂
                          → Vote.author v₁ ≡ a
                          → Vote.author v₂ ≡ a
                          → isHonestP ec a
                          → Vote.blockHash v₁ ≡ Vote.blockHash v₂

          The above would be simpler if messages had associated recipients, so we would just have
          a set of all messages ever sent by a given Author.  For this particular property, it
          does not matter whether the conflicting votes were sent to the same recipient or
          different.

  - Protocol vs. Algorithm

    We should aim for a clean separation between how authors *behave* as observed from outside, and
    how they might achieve that behavior.  For example, a dishonest node might sign two different
    votes for the same round, while an honest one will not.  This will be captured by the algorithm
    authors use (keep track of latest_voted_round, respect it when creating votes), but the
    observable behavior is about what Vote it communicates, not what it creates or how it decides to
    create them.
-}

  data MessagePool : Set where
    empty  : MessagePool
    insert : ∀ {s r : Author} (mp : MessagePool) → Message s r → MessagePool

  data _∈mp_ {s r : Author} (m : Message s r) : MessagePool → Set where
    here  : ∀ {s r : Author} {m′ : Message s r} {mp : MessagePool} → m ∈mp (insert mp m)
    there : ∀ {s′ r′ : Author} {m′ : Message s′ r′} {mp : MessagePool} → m ∈mp mp → m ∈mp (insert mp m′)

  record GlobalSystemState : Set where
    constructor gss
    field
      gssNodeStates  : Author → NodeState
      gssSmrContexts : Author → SmrContext -- Not sure if we need more than one
      gssMessagePool : MessagePool

  open GlobalSystemState

  initialGlobalState : GlobalSystemState
  initialGlobalState = {!!}
---------- Actions ---------

  processShouldNotifyLeader : Maybe Author → NodeState → MessagePool → MessagePool
  processShouldNotifyLeader nothing    _  mp = mp
  processShouldNotifyLeader (just ldr) ns mp = insert {nsLocalAuthor ns} {ldr} mp {!!}   -- TODO: Send DataSyncNotification to leader?

  processShouldBroadcast : Bool → NodeState → MessagePool → MessagePool
  processShouldBroadcast false _  mp = mp
  processShouldBroadcast true  ns mp = {!!}       -- TODO: Send DataSyncNotification to .. whom?  Containing what?
                                                   -- From p. 19: // Ask that we reshare the proposal. (proposed_block)
                                                   -- From p. 38  // Access the block proposed by the leader chosen by the Pacemaker (if any).

  processNodeUpdateActions : MessagePool → Author → NodeState → NodeUpdateActions → MessagePool
  processNodeUpdateActions mp₀ a ns (mkNodeUpdateAction ssu snl sb) =
    let mp₁ = processShouldNotifyLeader snl ns mp₀
        mp₂ = processShouldBroadcast    sb  ns mp₁
    in mp₂

---------- Actions and reachable states ----------
  -- Update a function of type A → B on one input, given a decidability instance for A's
  -- The syntax is slightly ugly, but I couldn't do better in reasonable time
  -- TODO: Move somewhere more generic
  _[_:=_,_] : {A : Set} {A₂ : Set}
             (f : A → A₂)
           → A → A₂
           → (_≟_ : (a₁ : A) → (a₂ : A) → (Dec (a₁ ≡ a₂)))
           → A → A₂
  _[_:=_,_] {A = A} {A₂ = A₂} f a₁ b _≟_ a₂
     with a₁ ≟ a₂
  ...| yes _ = b
  ...| no  _ = f a₂

  effUpdateNode : {a : Author} → (preState : GlobalSystemState) → GlobalSystemState
  effUpdateNode {a} pre =
    let nss₀  = gssNodeStates pre
        ns₀   = nss₀ a
        smrs₀ = gssSmrContexts pre
        smr₀  = smrs₀ a
        nt    = 0 -- TODO
        mp₀   = gssMessagePool pre
        ( ns₁ , ( smr₁ , nua )) = updateNode ns₀ nt smr₀
        mp₁   = processNodeUpdateActions mp₀ a ns₁ nua
        nss₁  = nss₀  [ a := ns₁  , _≟ℕ_  ]
        smrs₁ = smrs₀ [ a := smr₁ , _≟ℕ_  ]
    in gss nss₁ smrs₁ mp₁

  data ReachableState : (gss : GlobalSystemState) → Set where
    rchstEmpty      : ReachableState initialGlobalState
    rchstUpdateNode : ∀ {a : Author} {nt : NodeTime} {preState : GlobalSystemState} {preSmr : SmrContext}
                    → ReachableState preState
                    → ReachableState (effUpdateNode {a} preState)

---------- Properties that depend on algorithm (for honest authors only, of course) --------

  -- Section 5.4, p. 16
  -- [LIBRA-DIFF] The paper says: (increasing-round) An honest node that voted once for ?? in the
  -- past may only vote for ??′ if round(??) < round(??′).  WHat it really should say is that an
  -- honest node does not create different votes for the same round and block.  Nobody can tell what
  -- *order* the votes are created in.  Furthermore, it doesn't matter if an honest node *creates*
  -- contradictory votes.  What matters is if it *sends* them somewhere.

  -- TODO: The following is not quite right yet, because it applies to any EpochConfiguration.  So
  -- we could make up an EpochConfiguration in which some bad guy appears honest, and this property
  -- might not hold.  We will need something that ties ec to the epoch in question, which essentially
  -- says that ec is the "official" EpochConfiguration for that epoch.  This will be a function of
  -- committed state (platform data in the parlance of our ASAPD in Juno).
  honestVotesConsistent : ∀ {a : Author}
                            {ec : EpochConfiguration}
                            {m₁ m₂ : Message a _}
                            {v₁ v₂ : Vote}
                            {s : GlobalSystemState}
                          → ReachableState s
                          → m₁ ∈mp gssMessagePool s
                          → m₂ ∈mp gssMessagePool s
                          → (V v₁) ∈msg m₁
                          → (V v₂) ∈msg m₂
                          → Vote.epochId v₁ ≡ Vote.epochId v₂
                          → Vote.round v₁   ≡ Vote.round v₂
                          → isHonestP ec a
                          → Vote.blockHash v₁ ≡ Vote.blockHash v₂
  honestVotesConsistent = {!!}
