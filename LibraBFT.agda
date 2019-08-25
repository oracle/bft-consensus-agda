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

  record EpochConfiguration : Set₁ where
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
  record Block : Set where
    field
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
      bAuthor     : Author
      --bSignature  : Signature
  open Block

 -- Vote -------------------------------------------
  record Vote : Set where
    field
      vEpoch     : EpochId
      vRound     : Round
      vBlockHash : BlockHash
      vState     : State
      vAuthor    : Author
      vSignature : Signature
  open Vote


 -- QuorumCertificate ------------------------------
  record QC : Set where
  -- TODO: record QC (ec : EpochConfiguration) : Set where
    field
      qEpoch         : EpochId
      qBlockHash     : BlockHash
      qRound         : Round
      qState         : State
      qVotes         : List Vote
      qAuthor        : Author
  open QC

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

  -- Votes are on the chain?? I think it gets confusing having this predicate and also RecOrInit,
  -- I thinks votes can be on RecordStore but not in the chain
  data isChainableRecord : Record → Set where
    B : ∀ (b : Block) → isChainableRecord (B b)
    Q : ∀ (q : QC)    → isChainableRecord (Q q)
    --V : ∀ (v : Vote  ec) → isChainableRecord (V v)

  record Initial : Set where
    constructor mkInitial
    field
      epochId : EpochId
      seed    : ℕ

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
  ...| yes refl
       with seed i₁ ≟ seed i₂
  ...|   yes refl = yes refl
  ...|   no  xx1 = no (xx1 ∘ (cong seed))

  round : Record → Round
  round (B b) = Block.bRound b
  round (Q q) = QC.qRound q
  round (V v) = Vote.vRound v
  round (T t) = Timeout.toRound t

  data RecOrInit : Set where
    I : Initial → RecOrInit
    R : Record  → RecOrInit

 -- Hash Functions ----------------------------------------------
  postulate
    encodeR     : RecOrInit → ByteString
    encodeR-inj : ∀ {r₀ r₁ : RecOrInit} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR : RecOrInit → Hash
  HashR = hash ∘ encodeR


  -- 4.7. Mathematical Notations --------------------------------

  -- Definition of R₁ ← R₂
  data _←_ : RecOrInit → Record → Set where
    I←B : ∀ {i : Initial} {b : Block}
          → HashR (I i) ≡  bPrevQCHash b
          → I i ← B b
    Q←B : ∀ {q : QC} {b : Block}
          → HashR (R (Q q)) ≡  bPrevQCHash b
          → R (Q q) ← B b
    B←Q : ∀ {b : Block} {q : QC}
          → HashR (R (B b)) ≡ qBlockHash q
          → R (B b) ← Q q

  data _←⋆_ (r₁ : RecOrInit) (r₂ : Record) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : Record} → (r₁ ←⋆ r) → (R r ← r₂) → r₁ ←⋆ r₂


------------------------- RecordStore --------------------------

  data RecordStore (ec : EpochConfiguration) (sᵢ : Initial) : Set

  data Valid {ec : EpochConfiguration} {sᵢ : Initial} : Record → RecordStore ec sᵢ → Set

  data RecordStore ec sᵢ where
    empty  : RecordStore ec sᵢ
    insert : {r : Record} (s : RecordStore ec sᵢ)
             → Valid r s → RecordStore ec sᵢ

  data _∈Rs_ {ec} {sᵢ} : Record → RecordStore ec sᵢ → Set where
    here  : ∀ {s : RecordStore ec sᵢ} {r : Record} (v : Valid r s)
            → r ∈Rs insert s v
    there : ∀ {s : RecordStore ec sᵢ} {r r' : Record} (v : Valid r' s)
            → r ∈Rs s
            → r ∈Rs (insert s v)
    inQC  : ∀ {s : RecordStore ec sᵢ} {v : Vote} {qc : QC}
            → (Q qc) ∈Rs s
            --→ v ∈ (qVotes qc)
            → V v ∈Rs s

  qSize :  EpochConfiguration → ℕ
  qSize ec = ecN ec ∸ ecF ec

  _≡-Author_ : Vote → Vote → Set
  v₁ ≡-Author v₂ = vAuthor v₁ ≡ vAuthor v₂


  -- TODO: Validate records wrt epoch configuration
  ValidBlock : ∀ {ec} {sᵢ} → Block → RecordStore ec sᵢ → Set
  ValidBlock {ec} {sᵢ} b rs = ∃[ q ] ( q ∈Rs rs × Valid q rs × R q ← B b × round q < bRound b )
                              ⊎
                              I sᵢ ← B b × 1 ≤ bRound b

  _validVoteInQC_ : Vote → QC → Set
  v validVoteInQC qc = (vEpoch v ≡ qEpoch qc) × (vBlockHash v ≡ qBlockHash qc) × (vRound v ≡ qRound qc) × (vState v ≡ qState qc) -- × signature valid

  validQC_wrt_ : QC → EpochConfiguration → Set
  validQC q wrt ec = All (_validVoteInQC q) (qVotes q) × length (qVotes q) ≡ qSize ec

  -- TODO : Validate all Votes in a QC
  ValidQC : ∀ {ec} {sᵢ} → QC → RecordStore ec sᵢ → Set
  ValidQC {ec} q rs = ∃[ b ] ( b ∈Rs rs × Valid b rs × R b ← Q q × round b ≡ qRound q × validQC q wrt ec )


  -- Conditions required to add a Record to a RecordStore (which contained "previously verified"
  -- records, in the parlance of the LibraBFT paper.  Some properties do not depend on any
  -- particular RecordStore and their proofs can ignore the RecordStore, other than passing it to
  -- recursive invocations.

  data Valid {ec} {sᵢ} where
    ValidB : ∀ {b : Block} {rs : RecordStore ec sᵢ} → ValidBlock b rs → Valid (B b) rs
    ValidQ : ∀ {q : QC}    {rs : RecordStore ec sᵢ} → ValidQC    q rs → Valid (Q q) rs
    --ValidV : ∀ {v : Vote    ec} {rs : RecordStore ec sᵢ} → ValidVote  v rs → Valid (V v) rs
    --ValidT : ∀ {t : Timeout ec} {rs : RecordStore ec sᵢ}                   → Valid (T t) rs

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
  ←inj : ∀ {r₀ : RecOrInit} {r₁ r₂ : Record} → (r₀ ← r₂) → (R r₁ ← r₂)
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

  r₀←⋆r₁→rr₀≤rr₁ : ∀ {ec sᵢ} {r₀ r₁ : Record} {rs : RecordStore ec sᵢ}
                 → R r₀ ←⋆ r₁
                 → Valid r₁ rs
                 → round r₀ ≤ round r₁ ⊎ HashBroke
  r₀←⋆r₁→rr₀≤rr₁ (ss0 r₀←b) (ValidB prf)
     with prf
  ... | inj₁ ⟨ q , ⟨ q∈rs , ⟨ vQ , ⟨ q←b , rq<rb ⟩ ⟩ ⟩ ⟩
      with ←inj r₀←b q←b
  ...   | inj₁ refl      = inj₁ (<⇒≤ rq<rb)
  ...   | inj₂ hashbroke = inj₂ hashbroke
  r₀←⋆r₁→rr₀≤rr₁ (ss0 r₀←b) (ValidB prf)
      | inj₂ ⟨ i←b , 1≤rb ⟩
      with ←inj i←b r₀←b
  ...   | inj₂ hashbroke = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ (ss0 r₀←q) (ValidQ prf)
    with prf
  ... |   ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , ⟨ refl , snd ⟩ ⟩ ⟩ ⟩ ⟩
      with ←inj r₀←q b←q
  ...   | inj₁ refl            = inj₁ ≤-refl
  ...   | inj₂ hashbroke       = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ (ssr r₀←⋆r r←b) (ValidB prf)
    with prf
  ... | inj₁ ⟨ q , ⟨ q∈rs , ⟨ vQ , ⟨ q←b , rq<rb ⟩ ⟩ ⟩ ⟩
      with ←inj r←b q←b
  ...   | inj₂ hashbroke = inj₂ hashbroke
  ...   | inj₁ refl
        with  r₀←⋆r₁→rr₀≤rr₁ r₀←⋆r vQ
  ...     | inj₁ rr₀≤rq    = inj₁ (≤-trans rr₀≤rq (<⇒≤ rq<rb))
  ...     | inj₂ hashbroke = inj₂ hashbroke
  r₀←⋆r₁→rr₀≤rr₁ (ssr r₀←⋆r r←b) (ValidB prf)
      | inj₂ ⟨ i←b , 1≤rb ⟩
      with ←inj i←b r←b
  ...   | inj₂ hashbroke = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ (ssr r₀←⋆r r←q) (ValidQ prf)
    with prf
  ... | ⟨ b , ⟨ b∈rs , ⟨  vB , ⟨ b←q , ⟨ refl , snd ⟩ ⟩ ⟩ ⟩ ⟩
      with ←inj r←q b←q
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl
        with  r₀←⋆r₁→rr₀≤rr₁ r₀←⋆r vB
  ...     | inj₁ rr₀≤rq    = inj₁ rr₀≤rq
  ...     | inj₂ hashbroke = inj₂ hashbroke


  -- Lemma 1, part 3
  round-mono : ∀ {ec sᵢ} {r₀ r₁ r₂ : Record} {rs : RecordStore ec sᵢ}
                 → R r₀ ←⋆ r₂
                 → R r₁ ←⋆ r₂
                 → Valid r₀ rs → Valid r₁ rs → Valid r₂ rs
                 → round r₀ < round r₁
                 → (R r₀ ←⋆ r₁) ⊎ HashBroke

  round-mono (ss0 r₀←r₂)      (ss0 r₁←r₂)        _ _ _ rr₀<rr₁
    with ←inj r₀←r₂ r₁←r₂
  ... | inj₁ refl = ⊥-elim (<⇒≢ rr₀<rr₁ refl)
  ... | inj₂ hashbroke = inj₂ hashbroke

  round-mono (ss0 r₀←r₂)      (ssr r₁←⋆r′ r′←r₂) v₀ _ _ rr₀<rr₁
    with ←inj r₀←r₂ r′←r₂
  ... | inj₂ hashBroke                      = inj₂ hashBroke
  ... | inj₁ refl
      with r₀←⋆r₁→rr₀≤rr₁ r₁←⋆r′ v₀
  ...   |  inj₁ rr₁≤rr₀                     = ⊥-elim (≤⇒≯ rr₁≤rr₀ rr₀<rr₁)
  ...   |  inj₂ hashbroke                   = inj₂ hashbroke

  round-mono (ssr r₀←⋆r r←r₂) (ss0 r₁←r₂)        v₀ _ _ rr₀<rr₁
    with ←inj r₁←r₂ r←r₂
  ... | inj₁ refl                           = inj₁ r₀←⋆r
  ... | inj₂ hashBroke                      = inj₂ hashBroke

  round-mono (ssr r₀←⋆r r←r₂) (ssr r₁←⋆r′ r′←r₂) v₀ v₁ v₂ rr₀<rr₁
    with v₂
  ... | ValidB (inj₁ ⟨ q , ⟨ q∈rs , ⟨ vQ , ⟨ q←b , _ ⟩ ⟩ ⟩ ⟩ )
      with ←inj r←r₂ r′←r₂ | ←inj r←r₂ q←b
  ...    | inj₂ hashbroke  |  _             = inj₂ hashbroke
  ...    | inj₁ _          | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₁ refl       | inj₁ refl      = round-mono r₀←⋆r r₁←⋆r′ v₀ v₁ vQ rr₀<rr₁

  round-mono (ssr r₀←⋆r r←r₂) (ssr r₁←⋆r′ r′←r₂) _ _ _ rr₀<rr₁
      | ValidB (inj₂ ⟨ i←b , _ ⟩)
      with ←inj i←b r←r₂
  ...    | inj₂ hashbroke                   = inj₂ hashbroke

  round-mono (ssr r₀←⋆r r←r₂) (ssr r₁←⋆r′ r′←r₂) v₀ v₁ _ rr₀<rr₁
      | ValidQ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , _ ⟩ ⟩ ⟩ ⟩
      with ←inj r←r₂ r′←r₂ | ←inj r←r₂ b←q
  ...    | inj₂ hashbroke  |  _             = inj₂ hashbroke
  ...    | inj₁ _          | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₁ refl       | inj₁ refl      = round-mono r₀←⋆r r₁←⋆r′ v₀ v₁ vB rr₀<rr₁



------------------------ RecordStoreState ----------------------

  record RecordStoreState : Set₁ where
    field
      epoch       : EpochId
      epochConfig : EpochConfiguration
      sᵢ          : Initial
      recStore    : RecordStore epochConfig sᵢ
      curRound    : Round
      highQCR     : Round
      listVotes   : List Vote
      -- initialState : State
      -- highCommR    : Round
----------------------------------------------------------------

  open RecordStoreState

-------------------- Lemma S1, part 1 --------------------
  -- I think that Votes should not be in RecordStore because we have the List of Votes in the RecordStoreState
  -- which will have the list of votes received
  hᵢ←⋆R : ∀ {ec sᵢ} {r : Record} {rs : RecordStore ec sᵢ}
          → r ∈Rs rs
          → (I sᵢ) ←⋆ r
  hᵢ←⋆R (here (ValidB prf))
    with prf
  ... | inj₂ ⟨ i←b , _ ⟩ = ss0 i←b
  ... | inj₁ ⟨ q , ⟨ q∈rs , ⟨ vQ , ⟨ q←b , _ ⟩ ⟩ ⟩ ⟩ = ssr (hᵢ←⋆R q∈rs) q←b

  hᵢ←⋆R (here (ValidQ prf))
    with prf
  ... |      ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , _ ⟩ ⟩ ⟩ ⟩ = ssr (hᵢ←⋆R b∈rs) b←q

  hᵢ←⋆R (there vR r∈rs) = hᵢ←⋆R r∈rs

  hᵢ←⋆R (inQC x) = {!!}

  lemma1-1 : RecordStoreState → Set
  lemma1-1 rss = ∀ {r : Record}
               → r ∈Rs (recStore rss)
               → (I (sᵢ rss)) ←⋆ r

  record AuxRecordStoreState : Set₁ where
    field
      auxRssData     : RecordStoreState
      auxRssLemma1-1 : lemma1-1 auxRssData

-------------------- RecordStoreState tests --------------------

  rss1 : RecordStoreState
  rss1 = record {
             epoch       = 1
           ; epochConfig = ec1
           ; sᵢ          = record { epochId = 1 ; seed = 1 }
           ; recStore    = empty
           ; curRound    = 1
           ; highQCR     = 1 -- should this be a Maybe?
           ; listVotes   = []
         }

  arss1 : AuxRecordStoreState
  arss1 = record {
              auxRssData = rss1
            ; auxRssLemma1-1 = λ x → {!!} --contradiction x (λ ()) -- or  hᵢ←⋆R x
          }

  testInit : Initial
  testInit = record { epochId = 1
                    ; seed    = 1
                    }

  block1 : Block
  block1 = record { bCommand = 1
                  ; bRound = 1
                  ; bPrevQCHash = HashR (I testInit)
                  ; bAuthor = dummyAuthor 0
                  }

  rss2 : RecordStoreState
  rss2 = record rss1 { recStore = insert empty (ValidB (inj₂ ⟨ I←B {b = block1} refl , s≤s z≤n ⟩))}

  arss2 : AuxRecordStoreState
  arss2 = record {
              auxRssData = rss2
            ; auxRssLemma1-1 = λ x → hᵢ←⋆R x
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


  -- Define a notion of an author being "in" a quorum certificate for a given EpochConfiguration
  _∈Qs_for_ :  Author → QC → EpochConfiguration → Set
  a ∈Qs q for ec = {!!}

  -- Should be provable from constraints on EpochConfigurations
  BFTQuorumIntersection : (ec : EpochConfiguration)
                        → (q₁ q₂ : QC)
                        → validQC q₁ wrt ec
                        → validQC q₂ wrt ec
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

-------------------------- NodeState ---------------------------

  NodeTime : Set
  NodeTime = {!!}


  FakeTypeActiveNodes : Set
  FakeTypeActiveNodes = {!!}
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
  -- I think it sould also receive as a parameter the epoch configuration
  record NodeState : Set₁ where
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

  createTimeout' : ∀ {ec} {h} → RecordStore ec h → Author → Round → SmrContext → RecordStore ec h
  createTimeout' rs _ r _ = {!!} -- insert rs {! !} -- Can't prove valid to insert timeout until definitions fleshed out

  createTimeout : RecordStoreState → Author → Round → SmrContext → RecordStoreState
  createTimeout rss a r smr =
    record rss { recStore = createTimeout' {epochConfig rss} {sᵢ rss} (recStore rss) a r smr }

  createTimeoutCond : NodeState → Maybe Round → SmrContext → NodeState
  createTimeoutCond ns nothing  _   = ns
                                                                      -- TODO: after merging with Lisandra, naming conventions
  createTimeoutCond ns (just r) smr = record ns { nsRecordStore = createTimeout (NodeState.nsRecordStore ns) (author ns) r smr }

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

  -- fn process_pacemaker_actions( &mut self,
  --                               pacemaker_actions: PacemakerUpdateActions,
  --                               smr_context: &mut SMRContext,
  --                             ) -> NodeUpdateActions {
  processPacemakerActions :
      EpochConfiguration
    → NodeState
    → PacemakerUpdateActions
    → SmrContext
    → NodeState × SmrContext × NodeUpdateActions
  processPacemakerActions ec self₀ pacemakerActions smrContext₀ =
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

  -- fn update_node(&mut self, clock: NodeTime, smr_context: &mut SMRContext) -> NodeUpdateActions {
  updateNode : EpochConfiguration
             → NodeState
             → NodeTime
             → SmrContext
             → NodeState × SmrContext × NodeUpdateActions
  updateNode ec self₀ clock smrContext₀ =
    let

  -- let latest_senders = self.read_and_reset_latest_senders();
         --latestSenders = {!!}

  -- let pacemaker_actions = self.pacemaker.update_pacemaker( self.local_author, &self.record_store, self.latest_broadcast, latest_senders, clock,);
         pacemakerActions = {!!}

-- let mut actions = self.process_pacemaker_actions(pacemaker_actions, smr_context);
         -- Can't keep this organized as in paper, because can't do with & where here
         (self₁ , actions₀) = processPacemakerActions ec self₀ pacemakerActions smrContext₀

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
                   → {ec : EpochConfiguration}
                   → {h : Initial}
                   → RecordStore ec h
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

