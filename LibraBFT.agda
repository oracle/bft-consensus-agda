{-# OPTIONS --allow-unsolved-metas #-}

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
open import Data.Maybe.Properties using (just-injective)
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

  SmrContext : Set
  SmrContext = ℕ    -- TODO: placeholder

  -- Update a function of type A → B on one input, given a decidability instance for A's
  -- The syntax is slightly ugly, but I couldn't do better in reasonable time
  -- TODO: Move somewhere more generic

  overrideOK : {ℓ₁ ℓ₂ : Level.Level} {A : Set ℓ₁} {B : Set ℓ₂}
             → (f : A → B)
             → (a : A)
             → (b : B)
             → (a′ : A)
             → (f′ : A → B)
             → Set (ℓ₁ Level.⊔ ℓ₂)
  overrideOK f a b a′ f′ = (a′ ≢ a × f′ a′ ≡ f a′) ⊎ (a′ ≡ a × f′ a′ ≡ b)

  overrideProp : {ℓ₁ ℓ₂ : Level.Level} {A : Set ℓ₁} {B : Set ℓ₂}
               → (f : A → B)
               → (a : A)
               → (b : B)
               → (f′ : A → B)
               → Set (ℓ₁ Level.⊔ ℓ₂)
  overrideProp f a b f′ = ∀ a′ → overrideOK f a b a′ f′

  overrideFn : {ℓ₁ ℓ₂ : Level.Level} {A : Set ℓ₁} {B : Set ℓ₂}
             (f : A → B)
           → (a : A) → (b : B)
           → ((a₁ : A) → (a₂ : A) → (Dec (a₁ ≡ a₂)))
           → Σ ( A → B ) (λ f′ → overrideProp f a b f′)
  overrideFn {A = A} {B = B} f a b _≟xx_ =
     let f′ = (λ a₂ → selectVal f a b a₂)
     in f′ ,  (λ a₂ → selectPrf f a b a₂)

     where selectVal : (f : A → B) → (a : A) → (b : B) → (a₂ : A) → B
           selectVal f a b a₂ with a₂ ≟xx a
           ...| yes _ = b
           ...| no  _ = f a₂
           selectPrf : (f : A → B) → (a : A) → (b : B) → (a₂ : A) → overrideOK f a b a₂ (λ a₃ → selectVal f a b a₃)
           selectPrf f a b a₂ with a₂ ≟xx a
           ...| yes refl = inj₂ ⟨ refl , refl ⟩
           ...| no  a₂≢a = inj₁ ⟨ a₂≢a , refl ⟩

  _[_:=_,_] : {ℓ₁ ℓ₂ : Level.Level} {A : Set ℓ₁} {B : Set ℓ₂}
             (f : A → B)
           → (a : A) → (b : B)
           → (_≟_ : (a₁ : A) → (a₂ : A) → (Dec (a₁ ≡ a₂)))
           → Σ ( A → B ) (λ f′ → overrideProp f a b f′)
  _[_:=_,_] {ℓ₁} {ℓ₂} {A = A} {B = B} f a₁ b _≟xx_ = overrideFn {ℓ₁} {ℓ₂} {A} {B} f a₁ b _≟xx_


  HashMap : Set → Set → Set
  HashMap K V = K → Maybe V

  emptyHM : ∀ {K V : Set} → HashMap K V
  emptyHM {K} {V} k = nothing

  _∈HM_ : ∀ {K : Set} {V : Set} (k : K) → HashMap K V → Set
  k ∈HM hm = ∃[ v ]( hm k ≡ just v )

  emptyIsEmpty : ∀ {K : Set} {V : Set} {k : K} → ¬ (k ∈HM emptyHM {K} {V})
  emptyIsEmpty {k = k} = λ ()

---------------------- Move somewhere more generic --------------

  nothing≢just : ∀ {ℓ : Level.Level} {A : Set ℓ} {a : A} → nothing ≡ just a → ⊥
  nothing≢just = λ ()

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

 --------------------------- Record -----------------------------

 -- Block ------------------------------------------
  record Block : Set where
    constructor mkBlock
    field
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
      bAuthor     : Author
      --bSignature  : Signature
  open Block

  ≡Block : ∀ {b₁ b₂ : Block}
         → {cmd₁ cmd₂ : Command } → cmd₁ ≡ cmd₂
         → {h₁ h₂     : QCHash  } → h₁   ≡ h₂
         → {r₁ r₂     : Round   } → r₁   ≡ r₂
         → {a₁ a₂     : Author  } → a₁   ≡ a₂
         → mkBlock cmd₁ h₁ r₁ a₁ ≡
           mkBlock cmd₂ h₂ r₂ a₂
  ≡Block refl refl refl refl = refl

  _≟Block_ : (b₁ b₂ : Block) → Dec (b₁ ≡ b₂)


 -- Vote -------------------------------------------
  record Vote : Set where
    field
      vEpoch     : EpochId
      vRound     : Round
      vBlockHash : BlockHash
      --vState     : State
      vAuthor    : Author
      vSignature : Signature
  open Vote

 -- QuorumCertificate ------------------------------
  record QC : Set where
    field
      qEpoch         : EpochId
      qBlockHash     : BlockHash
      qRound         : Round
      --qState         : State
      qVotes         : List Vote
      qAuthor        : Author
  open QC

  -- The hash of this structure will be the root of RecordStore. With this defintion we can
  -- represent the depends relation r₁ ← r₂, which means hash r₁ = prevHash r₂, where r₁ can
  -- be a chainable record as a Block or QC but can also be this Initial structure (which only
  -- a Block can extend, see definition of _←_)
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
  open Timeout

  data Record : Set where
    B : Block   → Record
    Q : QC      → Record
    V : Vote    → Record
    T : Timeout → Record

  data isChainableRecord : Record → Set where
    B : ∀ (b : Block) → isChainableRecord (B b)
    Q : ∀ (q : QC)    → isChainableRecord (Q q)
    --V : ∀ (v : Vote  ec) → isChainableRecord (V v)

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
  ...| yes refl
       with seed i₁ ≟ seed i₂
  ...|   yes refl = yes refl
  ...|   no  xx1 = no (xx1 ∘ (cong seed))

  --TODO : Delete this function
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
    B←V : ∀ {b : Block} {v : Vote}
          → HashR (R (B b)) ≡ vBlockHash v
          → R (B b) ← V v

  data _←⋆_ (r₁ : RecOrInit) (r₂ : Record) : Set where
    ss0 : (r₁ ← r₂) → r₁ ←⋆ r₂
    ssr : ∀ {r : Record} → (r₁ ←⋆ r) → (R r ← r₂) → r₁ ←⋆ r₂

  qSize :  EpochConfiguration → ℕ
  qSize ec = ecN ec ∸ ecF ec

  _≡-Author_ : Vote → Vote → Set
  v₁ ≡-Author v₂ = vAuthor v₁ ≡ vAuthor v₂

------------------------ RecordStoreState ----------------------

  record RecordStoreState : Set₁ where
    constructor mkRecordStoreState
    field
      rssEpochId              : EpochId
      rssConfiguration        : EpochConfiguration
      rssInitial              : Initial  -- LIBRA-DIFF, we store the Initial structure;
                                         -- Libra say QuorumCertificateHash, but it's not really one.
      -- rssInitiaState       : State
      rssBlocks               : HashMap BlockHash Block
      rssQCs                  : HashMap QCHash QC
      rssRoundToQChash        : HashMap Round QCHash
      rssCurrentProposedBlock : Maybe BlockHash
      rssHighestQCRound       : Round
      -- rssHighestTCRound    : Round
      rssCurrentRound         : Round
      -- rssHighest2ChainRound       : Round
      -- rssHighestCommittedRound    : Round
      -- rssHighestTimoutCertificate : Maybe (List Timeout)
      rssCurrentTimeouts      : HashMap Author Timeout
      rssCurrentVotes         : HashMap Author Vote
      -- rssCurrentTimeoutWeight     : ℕ  -- LIBRA-DIFF: assume equal weights for now
      -- rssCurrentElection          : ?

  open RecordStoreState

  emptyRSS : EpochId → EpochConfiguration → Initial → RecordStoreState
  emptyRSS eid ecfg init = record {
      rssEpochId              = eid
    ; rssConfiguration        = ecfg
    ; rssInitial              = init
      -- rssInitiaState   : State
    ; rssBlocks               = emptyHM
    ; rssQCs                  = emptyHM
    ; rssRoundToQChash        = proj₁ (emptyHM [ 0 := just (HashR (I init)) , _≟ℕ_ ])
    ; rssCurrentProposedBlock = nothing
    ; rssHighestQCRound       = 0
      -- rssHighestTCRound    = 0
    ; rssCurrentRound         = 1
      -- rssHighest2ChainRound   : Round
      -- rssHighestCommittedRound : Round
      -- rssHighestTimoutCertificate : Maybe (List Timeout)
    ; rssCurrentTimeouts      = emptyHM
    ; rssCurrentVotes         = emptyHM
      -- rssCurrentTimeoutWeight : ℕ  -- LIBRA-DIFF: assume equal weights for now
      -- rssCurrentElection : ?
    }

----------------------------------------------------------------
  _∈QC_ : Vote → QC → Set
  v ∈QC q = {!!} -- v ∈ qVotes q     TODO: (Lisandra) fix missing definition

  -- I would colapse this 2 defintions into one   TODO: (Lisandra) sounds good
  _∈Rs′_ : Record → RecordStoreState → Set
  (B b) ∈Rs′ rss = ∃[ h ](rssBlocks          rss h ≡ just b)
  (Q q) ∈Rs′ rss = ∃[ h ](rssQCs             rss h ≡ just q)
  (V v) ∈Rs′ rss = ∃[ a ](rssCurrentVotes    rss a ≡ just v)
  (T t) ∈Rs′ rss = ∃[ a ](rssCurrentTimeouts rss a ≡ just t)

  _∈Rs_ : ∀ (r : Record) → RecordStoreState → Set
  (B b) ∈Rs rss = (B b) ∈Rs′ rss
  (Q q) ∈Rs rss = (Q q) ∈Rs′ rss
  (V v) ∈Rs rss = (V v) ∈Rs′ rss ⊎ ∃[ q ] ((Q q) ∈Rs′ rss × v ∈QC q )
  (T t) ∈Rs rss = (T t) ∈Rs′ rss

  _≟BlockMB_ : (bMB₁ bMB₂ : Maybe Block) → Dec (bMB₁ ≡ bMB₂)
  _≟BlockMB_ = Data.Maybe.Properties.≡-dec  _≟Block_


  -- TODO: decidability instance is tricky because we need to capture the fact that a HashMap
  -- uses the hash of the value as the key, which so far is not stated anywhere.  Without this,
  -- we cannot prove that Record r is not in the Hashmap with some key other than HashR (R r).
  _∈Rs?_ : ∀ (r : Record) → (rss : RecordStoreState) → Dec (r ∈Rs rss)
  (B b) ∈Rs? rss with ((rssBlocks rss) (HashR (R (B b)))) ≟BlockMB just b
  ...|             no  xx = no  ( λ x → ⊥-elim (xx {! !}))
  ...|             yes xx = yes  ((HashR (R (B b))) , xx )
  (Q q) ∈Rs? rss = {!!}
  (V v) ∈Rs? rss = {!!} -- NOTE: not sure we'll need an instance here
  (T t) ∈Rs? rss = {!!} -- NOTE: not sure we'll need an instance here

  data _∈RsHash_ (h : Hash) (rss : RecordStoreState) : Set where
    I :         HashR (I (rssInitial rss)) ≡ h        → h ∈RsHash rss
    B : ∃[ b ] (HashR (R (B b)) ≡ h × (B b) ∈Rs rss ) → h ∈RsHash rss
    Q : ∃[ q ] (HashR (R (Q q)) ≡ h × (Q q) ∈Rs rss ) → h ∈RsHash rss

  -- These simply insert records into the RecordStoreState; it says nothing about Valid conditions, which is reserved for
  -- inserting into an AuxRecordStoreState that maintains invariants about the contents of the RecordStoreState.
  rssInsert : Record → RecordStoreState → RecordStoreState
  rssInsert (B b) rs = record rs { rssBlocks          = proj₁ ((rssBlocks rs)          [ (HashR (R (B b))) := (just b) , _≟Hash_ ]) }
  rssInsert (Q q) rs = record rs { rssQCs             = proj₁ ((rssQCs rs)             [ (HashR (R (Q q))) := (just q) , _≟Hash_ ]) }
  rssInsert (V v) rs = record rs { rssCurrentVotes    = proj₁ ((rssCurrentVotes rs)    [ (Vote.vAuthor v)  := (just v) , _≟ℕ_    ]) }
  rssInsert (T t) rs = record rs { rssCurrentTimeouts = proj₁ ((rssCurrentTimeouts rs) [ (toAuthor t)      := (just t) , _≟ℕ_    ]) }
                                                                                        -- Why is the Author the key for the Timeout
  memberAfterInsert : ∀ {b : Block} {rss : RecordStoreState}
                    → (B b) ∈Rs (rssInsert (B b) rss)
  memberAfterInsert {b} {rss} = ⟨ HashR (R (B b)) , prf b rss ⟩
     where prf : ∀ (b0 : Block)
               → (rss0 : RecordStoreState)
               → rssBlocks (rssInsert (B b0) rss0) (HashR (R (B b0))) ≡ just b0
           prf b0 rss0 with (HashR (R (B b0))) ≟Hash (HashR (R (B b0)))
           ...|          yes _  = refl
           ...|          no  xx = ⊥-elim (xx refl)

  data Valid : Record → RecordStoreState → Set


  _validVoteInQC_ : Vote → QC → Set
  v validVoteInQC qc = (vEpoch v ≡ qEpoch qc) × (vBlockHash v ≡ qBlockHash qc) × (vRound v ≡ qRound qc) --× (vState v ≡ qState qc)


{- TODO: (Lisandra) fix missing definition
  _distinctElemsIn_ : {A : Set} → ℕ → List A → Set
  size distinctElemsIn [] = size ≡ 0
  size distinctElemsIn (x ∷ x₁) = x ∉ x₁ × ((size ∸ 1) distinctElemsIn x₁)
-}

  validQC_wrt_ : QC → EpochConfiguration → Set
  validQC q wrt ec = {- TODO: (Lisandra) fix missing definitiomn
                     (qSize ec) distinctElemsIn (qVotes q)
                   × -}  
                     All (λ x → isVoter ec (vAuthor x) ≡ true) (qVotes q)
                     -- × Valid Signature

  --TODO : Validate signatures
  ValidBlock : Block → RecordStoreState → Set
  ValidBlock b rss = ∃[ q ] ( Q q ∈Rs rss × R (Q q) ← B b × qRound q < bRound b )
                     ⊎
                     I (rssInitial rss) ← B b × 1 ≤ bRound b

  -- TODO : Validate all Votes in a QC
  ValidQC : QC → RecordStoreState → Set
  ValidQC q rss = ∃[ b ] ( (B b) ∈Rs rss × R (B b) ← Q q × bRound b ≡ qRound q )
                  × All (_validVoteInQC q) (qVotes q)
                  × validQC q wrt (rssConfiguration rss)

  ValidVote : Vote → RecordStoreState → Set
  ValidVote v rss = ∃[ q ] ( Q q ∈Rs rss {- TODO: (Lisandra) restore this × v ∈ qVotes q -} )


  -- Conditions required to add a Record to a RecordStoreState (which contains "previously verified"
  -- records, in the parlance of the LibraBFT paper).  Some properties do not depend on any
  -- particular RecordStoreState and their proofs can ignore the RecordStoreState, other than passing it to
  -- recursive invocations.
  data Valid where
    ValidB : ∀ {b : Block} {rss : RecordStoreState} → ValidBlock b rss → Valid (B b) rss
    ValidQ : ∀ {q : QC}    {rss : RecordStoreState} → ValidQC    q rss → Valid (Q q) rss
    ValidV : ∀ {v : Vote}  {rss : RecordStoreState} → ValidVote  v rss → Valid (V v) rss
    --T : ∀ (t : Timeout) (rss : RecordStoreState)                     → Valid (T t) rss -- They are excluded from lemma s1

------------------------ RecordStoreState propereties --------------------

  lemma1-1 : RecordStoreState → Set
  lemma1-1 rss = ∀ {r : Record} {isCR : isChainableRecord r}
               → r ∈Rs rss
               → (I (rssInitial rss)) ←⋆ r

  highestQCHashExists : RecordStoreState → Set
  highestQCHashExists rss = ∃[ q ] (q ∈RsHash rss × rssRoundToQChash rss (rssHighestQCRound rss) ≡ just q)

  -- Given a RecordStoreState, auxiliary properties about it
  record AuxRecordStoreState (rss : RecordStoreState) : Set₁ where
    field
      auxRssLemma1-1  : lemma1-1 rss
      auxRss∃QCHash   : highestQCHashExists rss

  open AuxRecordStoreState


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

  ←inj {b₀} {b₁} {v} (B←V b₀←v) (B←V b₁←v)
     with hash-cr (trans b₀←v (sym b₁←v))
  ... | inj₁ ⟨ b₀≢b₁ , hb₀←hb₁ ⟩
             = inj₂ ⟨ ⟨ encodeR b₀ , encodeR (R b₁) ⟩ , ⟨ b₀≢b₁ , hb₀←hb₁ ⟩ ⟩
  ... | inj₂ b₀≡b₁
             = inj₁ (encodeR-inj b₀≡b₁)

  -- 3
  v∈q⇒b←v : ∀ {r q v}
            → R r ← (Q q)
            → vBlockHash v ≡ qBlockHash q
            → R r ← V v
  v∈q⇒b←v (B←Q refl) refl = B←V refl

  -- Aux Lemma
  -- This property does not depend on any particular RecordStore, and referring
  -- to it will unnecessarily complicate proofs.  The parameters is needed for
  -- recursive invocations of Valid, so it it provided but named "doNotUse" as
  -- a reminder.
  r₀←⋆r₁→rr₀≤rr₁ : {r₀ r₁ : Record}{doNotUse : RecordStoreState}
                 → R r₀ ←⋆ r₁
                 → Valid r₁ doNotUse
                 → round r₀ ≤ round r₁ ⊎ HashBroke
  r₀←⋆r₁→rr₀≤rr₁ (ss0 r₀←b) (ValidB prf) = {!!}
{- TODO: (Lisandra) restore after getting witness definition
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
  ... |   ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , _ ⟩
      with ←inj r₀←q b←q
  ...   | inj₁ refl            = inj₁ ≤-refl
  ...   | inj₂ hashbroke       = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ (ss0 r₀←v) (ValidV prf)
    with prf
  ... | ⟨ q , ⟨ q∈rs , ⟨ vQ , v∈q ⟩ ⟩ ⟩
      with vQ
  ...   | ValidQ ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , ⟨ validVotes , _ ⟩ ⟩
        with witness v∈q validVotes
  ...     | ⟨ _ , ⟨ hq≡hv , refl ⟩ ⟩
         with ←inj r₀←v (v∈q⇒b←v b←q hq≡hv)
  ...      | inj₁ refl      = inj₁ ≤-refl
  ...      | inj₂ hashbroke = inj₂ hashbroke

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
  ... |  ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , _ ⟩
      with ←inj r←q b←q
  ...   | inj₂ hashbroke       = inj₂ hashbroke
  ...   | inj₁ refl
        with  r₀←⋆r₁→rr₀≤rr₁ r₀←⋆r vB
  ...     | inj₁ rr₀≤rq    = inj₁ rr₀≤rq
  ...     | inj₂ hashbroke = inj₂ hashbroke

  r₀←⋆r₁→rr₀≤rr₁ (ssr r₀←⋆r r←v) (ValidV prf)
    with prf
  ... | ⟨ q , ⟨ q∈rs , ⟨ vQ , v∈q ⟩ ⟩ ⟩
      with vQ
  ...   | ValidQ ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , ⟨ validVotes , _ ⟩ ⟩
        with witness v∈q validVotes
  ...     | ⟨ _ , ⟨ hq≡hv , refl ⟩ ⟩
         with ←inj r←v (v∈q⇒b←v b←q hq≡hv)
  ...      | inj₂ hashbroke = inj₂ hashbroke
  ...      | inj₁ refl
           with  r₀←⋆r₁→rr₀≤rr₁ r₀←⋆r vB
  ...        | inj₁ rr₀≤rq    = inj₁ rr₀≤rq
  ...        | inj₂ hashbroke = inj₂ hashbroke
-}

  -- Lemma 1, part 3
  -- This property does not depend on any particular RecordStore, and referring
  -- to it will unnecessarily complicate proofs.  The parameters is needed for
  -- recursive invocations of Valid, so it it provided but named "doNotUse" as
  -- a reminder.
  round-mono : ∀  {r₀ r₁ r₂ : Record} {doNotUse : RecordStoreState}
                 → R r₀ ←⋆ r₂
                 → R r₁ ←⋆ r₂
                 → Valid r₀ doNotUse
                 → Valid r₁ doNotUse
                 → Valid r₂ doNotUse
                 → round r₀ < round r₁
                 → (R r₀ ←⋆ r₁) ⊎ HashBroke
  round-mono (ss0 r₀←r₂)      (ss0 r₁←r₂)        _ _ _ rr₀<rr₁ = {!!}
{- TODO: (Lisandra) restore after getting witness definition
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
      | ValidQ  ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , _ ⟩
      with ←inj r←r₂ r′←r₂ | ←inj r←r₂ b←q
  ...    | inj₂ hashbroke  |  _             = inj₂ hashbroke
  ...    | inj₁ _          | inj₂ hashbroke = inj₂ hashbroke
  ...    | inj₁ refl       | inj₁ refl      = round-mono r₀←⋆r r₁←⋆r′ v₀ v₁ vB rr₀<rr₁

  round-mono (ssr r₀←⋆r r←r₂) (ssr r₁←⋆r′ r′←r₂) v₀ v₁ v₂ rr₀<rr₁
      | ValidV ⟨ q , ⟨ q∈rs , ⟨ vQ , v∈q ⟩ ⟩ ⟩
      with vQ
  ...    | ValidQ ⟨ ⟨ b , ⟨ b∈rs , ⟨ vB , ⟨ b←q , refl ⟩ ⟩ ⟩ ⟩ , ⟨ validVotes , _ ⟩ ⟩
         with witness v∈q validVotes
  ...      | ⟨ _ , ⟨ hq≡hv , refl ⟩ ⟩
           with ←inj r←r₂ r′←r₂ | ←inj r←r₂ (v∈q⇒b←v b←q hq≡hv)
  ...         | inj₂ hashbroke  |  _             = inj₂ hashbroke
  ...         | inj₁ _          | inj₂ hashbroke = inj₂ hashbroke
  ...         | inj₁ refl       | inj₁ refl      = round-mono r₀←⋆r r₁←⋆r′ v₀ v₁ vB rr₀<rr₁
-}

-------------------- Lemma S1, part 1 --------------------

  -- TODO: this is broken now.  We need to extend the auxRecordStoreState with a proof,
  -- and use it inductively

  hᵢ←⋆R : ∀ {r : Record} {isCR : isChainableRecord r} {rs : RecordStoreState}
          → r ∈Rs rs
          → (I (rssInitial rs)) ←⋆ r
  hᵢ←⋆R = {!!}
{-
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
-}

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
  FakeTypeActiveNodes = List Author  -- TODO: Paper says HashSet<Author>

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
    constructor mkPacemakerState
    field
      pmsActiveRound       : Round
      pmsActiveLeader      : Maybe Author
      pmsActiveRoundStart  : NodeTime
      pmsActiveNodes       : FakeTypeActiveNodes
      pmsBroadcastInterval : Duration
      pmsDelta             : Duration
      pmsGamma             : GammaType

  pm0 : PacemakerState
  pm0 = mkPacemakerState 0 nothing 0 [] 0 0 0

  open PacemakerState

  -- Section 5.6, page 17
  record NodeState : Set₁ where
    constructor mkNodeState
    field
      nsRecordStoreState    : RecordStoreState
      nsPaceMaker           : PacemakerState
      nsEpochId             : EpochId
      nsLocalAuthor         : Author
      -- latestVotedRound : Round
      nsLockedRound         : Round
      nsLatestBroadcast     : NodeTime
      -- nsLatestSenders    : LatestSenders
      -- nsTracker          : DataTracker
      -- nsPastRecordStores : EpochId → RecordStoreState  -- How to model map?  AVL?  Homegrown?

  open NodeState

  record AuxValidNodeState (ns : NodeState) : Set₁ where
    field
      auxNsValidRSS : AuxRecordStoreState (nsRecordStoreState ns)

  open AuxValidNodeState

---------------------- Update Skeleton ----------------

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

  data AuxValidPacemakerUpdateActions (pma : PacemakerUpdateActions) (rss : RecordStoreState ) : Set where
    auxValidPMSBlockInRS : ∀ {qch : QCHash}
                           → puaShouldProposeBlock pma ≡ just qch
                           → qch ∈RsHash rss
                           → AuxValidPacemakerUpdateActions pma rss

  data AuxProposeBlockCondQCH (rss : RecordStoreState ) (qchMB : Maybe QCHash) : Set where
    auxProposeBlockInit : ∀ {qch : QCHash} → qchMB ≡ just (HashR (I (rssInitial rss))) → AuxProposeBlockCondQCH rss qchMB
    auxProposeBlockQC   : ∀ {qch : QCHash} → qchMB ≡ just qch → qch ∈RsHash rss        → AuxProposeBlockCondQCH rss qchMB

  open AuxValidPacemakerUpdateActions

---------------------- Libra BFT Algorithm components ---------------

  proposeBlockPrf : (b   : Block)
                  → (rss : RecordStoreState)
                  → AuxRecordStoreState rss
                  → AuxProposeBlockCondQCH rss (just (bPrevQCHash b))
                  → ValidBlock b rss
  proposeBlockPrf b rss _      (auxProposeBlockInit qchIsInit) =
                    inj₂ ( I←B (sym (just-injective qchIsInit)) , {!!} )
  proposeBlockPrf b rss auxRss (auxProposeBlockQC refl (Q ( qc , (qcHash , qcRec)))) =
                    inj₁ ((qc , (qcRec , ⟨ (Q←B qcHash) , {!!} ⟩ )))              -- TODO: round number property
  proposeBlockPrf b rss _      (auxProposeBlockQC refl (I x₁)) = ⊥-elim {!x₁!}   -- TODO: these cases can't happen unless HashBroke because
  proposeBlockPrf b rss _      (auxProposeBlockQC refl (B x₁)) = ⊥-elim {!!}     -- bPrevQCHash b is the hash of a QC, but we don't know
                                                                                  -- that here because our types do not distinguish the hashes
                                                                                  -- of different records (see comment in proposeBlock)

  proposeBlock : (rss : RecordStoreState)
               → Author
               → Command
               → (qch : QCHash)  -- TODO: this might be an initial hash, not a QCHash, but our types don't currently make a distinction
               → NodeTime        --       email discussion "Agdification: comment on Haskell version", maybe preimage should be auxiliary data
               → SmrContext
               → AuxRecordStoreState rss
               → AuxProposeBlockCondQCH rss (just qch)
               → Σ ( Block × BlockHash ) ( λ x → ValidBlock (proj₁ x) rss)
  proposeBlock rss a cmd qch nt smr auxPreRSS auxPbCondPrf =
    let rnd = rssCurrentRound rss
        b = mkBlock cmd qch rnd a  -- TODO: other fields
    in (( b , HashR (R (B b)) ) , proposeBlockPrf b rss auxPreRSS auxPbCondPrf)


  lemma11Block : ∀ {rss₀ : RecordStoreState}
                → lemma1-1 rss₀
                → {b : Block}
                → ValidBlock b rss₀
                → lemma1-1 (rssInsert (B b) rss₀)
  lemma11Block {rss₀} l1Pre {b} (inj₁ ( q , ( q∈rs , ( depPrf , rndPrf )))) {B b′} with b′ ≟Block b
  ...| yes xx1 rewrite xx1 = λ x → ssr (l1Pre {Q q} {Q q} q∈rs) depPrf
  ...| no  xx1 with (B b′) ∈Rs? rss₀
  ...|           yes xx2 = λ _ → l1Pre {B b′} {B b′} xx2
  ...|           no  xx2 = {!!}   -- TODO: b′ was not in rss before, and b′ ≢ b, so it's not in after either...

  proposeBlockCond : Author
                   → NodeTime
                   → (rss : RecordStoreState)
                   → (qchMB : Maybe QCHash)
                   → SmrContext
                   → AuxRecordStoreState rss
                   → AuxProposeBlockCondQCH rss qchMB
                   → Σ ( RecordStoreState × SmrContext ) ( λ x → AuxRecordStoreState (proj₁ x) )
  proposeBlockCond _ _         rss₀ nothing    smr auxPreRss   _            = ((rss₀ , smr) , auxPreRss)
  proposeBlockCond a ltstBcast rss₀ (just qch) smr auxValidRss auxPbCondPrf =
    let ((blk , blkHash) , blkPrf ) = proposeBlock
                                        rss₀
                                        a
                                        0 -- TODO: Real Commands
                                        qch
                                        ltstBcast
                                        smr
                                        auxValidRss
                                        auxPbCondPrf
        rss₁ = rssInsert (B blk) rss₀
        auxRSSValid₁ : AuxRecordStoreState rss₁
        auxRSSValid₁ = record { auxRssLemma1-1 = lemma11Block {rss₀} (auxRssLemma1-1 auxValidRss) {blk} blkPrf
                              ; auxRss∃QCHash  = {! auxRss∃QCHash {rss₀}  auxValidRss !} -- DITTO
                              }
    in ((rss₁ , smr) , auxRSSValid₁)

{-
  createTimeout' : ∀ {h} → RecordStore h → Author → Round → SmrContext → RecordStore h
  createTimeout' rs _ r _ = insert rs {! !} -- Can't prove valid to insert timeout until definitions fleshed out

  createTimeout : RecordStoreState → Author → Round → SmrContext → RecordStoreState
  createTimeout rss a r smr =
    record rss { recStore = createTimeout' {epochConfig rss} {sᵢ rss} (recStore rss) a r smr }

  createTimeoutCond : NodeState → Maybe Round → SmrContext → NodeState
  createTimeoutCond ns nothing  _   = ns
  createTimeoutCond ns (just r) smr = record ns { nsRecordStoreState = createTimeout (nsRecordStoreState ns) (nsLocalAuthor ns) r smr }
-}

  -- TODO: figure out idiomatic way to extract value from maybe given a proof it is just something.
  -- If nothing else, this could be refactored to mark it more generic so it can be used in other similar cases.
  extractQch : (qchMB : Maybe QCHash)
             → {pma : PacemakerUpdateActions}
             → puaShouldProposeBlock pma ≡ qchMB
             → {ns : NodeState}
             → AuxValidPacemakerUpdateActions pma (nsRecordStoreState ns)
             → AuxProposeBlockCondQCH (nsRecordStoreState ns) qchMB
  extractQch nothing    refl (auxValidPMSBlockInRS xx _) = ⊥-elim (nothing≢just xx)
  extractQch (just qch) refl {ns = ns} (auxValidPMSBlockInRS xx yy) =
                                        auxProposeBlockQC {nsRecordStoreState ns} {just qch} {qch} refl
                                                             (subst (_∈RsHash (nsRecordStoreState ns)) (sym (just-injective xx)) yy)

  -- fn process_pacemaker_actions( &mut self,
  --                               pacemaker_actions: PacemakerUpdateActions,
  --                               smr_context: &mut SMRContext,
  --                             ) -> NodeUpdateActions {

  processPacemakerActions :
      (ns : NodeState)
    → AuxValidNodeState ns
    → (pma : PacemakerUpdateActions)
    → AuxValidPacemakerUpdateActions pma (nsRecordStoreState ns)
    → SmrContext
    → Σ ( NodeState × SmrContext × NodeUpdateActions ) ( λ x → AuxValidNodeState (proj₁ x) )
  processPacemakerActions self₀ auxPreValidNS pacemakerActions auxPMAValid smrContext₀ =
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
      self₁ = self₀ -- TODO createTimeoutCond self₀ round smrContext₀

  -- if let Some(previous_qc_hash) = pacemaker_actions.should_propose_block {
      prevQCHashMB = puaShouldProposeBlock pacemakerActions

      auxPrevQCHprf = extractQch prevQCHashMB {pacemakerActions} refl {self₁} auxPMAValid

  --   self.record_store.propose_block(
  --       self.local_author,
  --       previous_qc_hash,
  --       self.latest_broadcast,
  --       smr_context,
  --   );
      -- TODO: we may need to modify the SMR context inside proposeBlock.  It's going to get
      -- painful here, as we will need to update both self amd SMR Context, based on the same
      -- condition
      ((rss₂ , smrContext₁) , postValidRss) = proposeBlockCond (nsLocalAuthor self₁)
                                                               (nsLatestBroadcast self₁)
                                                               (nsRecordStoreState self₁)
                                                               prevQCHashMB
                                                               smrContext₀
                                                               (auxNsValidRSS auxPreValidNS)
                                                               auxPrevQCHprf

      self₂ = record self₁ { nsRecordStoreState = rss₂ }
      postValidNS = record { auxNsValidRSS = postValidRss }

  -- }
  -- actions
  -- } }

    in (self₂ , (smrContext₁ , actions)) ,  postValidNS  -- TODO: Actions not updated yet

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
                  ; pmsActiveLeader = just clock
  --    // .. reset the set of nodes known to have entered this round (useful for leaders).
  --    self.active_nodes = HashSet::new();
                  ; pmsActiveNodes = []
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
                  → (rss : RecordStoreState)
                  → NodeTime
                  → LatestSenders
                  → NodeTime
                  → AuxRecordStoreState rss
                  → Σ ( PacemakerState × PacemakerUpdateActions ) (λ x → AuxValidPacemakerUpdateActions (proj₂ x) rss)
  updatePacemaker self₀ localAuthor recordStore latestBroadcast₀ latestSenders clock auxPreRSS =

     let
  --  // Initialize actions with default values.
  --  let mut actions = PacemakerUpdateActions::new();
       actions₀ = PacemakerUpdateActions∷new

  --  // Recompute the active round.
  --  let active_round = std::cmp::max(record_store.highest_quorum_certificate_round(), record_store.highest_timeout_certificate_round(),) + 1;
       activeRound = clock

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

       ( highQCH , highQCHprf )   = auxRss∃QCHash auxPreRSS
       actions₂    = record actions₁ { puaShouldProposeBlock = just highQCH }  -- TODO: this is unconditional for now, does not reflect algorithm
       auxValidPUA = auxValidPMSBlockInRS {actions₂} {recordStore} {proj₁ (auxRss∃QCHash auxPreRSS)} refl (proj₁ highQCHprf)

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
       actionsFinal = actions₂
     in (( pmFinal , actionsFinal ) , auxValidPUA)

----------------------------- updateNode ------------------------

  -- fn update_node(&mut self, clock: NodeTime, smr_context: &mut SMRContext) -> NodeUpdateActions {
  updateNode : (ns : NodeState)
             → NodeTime
             → SmrContext
             → AuxValidNodeState ns
             → Σ ( NodeState × SmrContext × NodeUpdateActions) (λ x → AuxValidNodeState (proj₁ x))
  updateNode self₀ clock smrContext₀ auxPreNS =
    let

  -- let latest_senders = self.read_and_reset_latest_senders();
         latestSenders = []

  -- let pacemaker_actions = self.pacemaker.update_pacemaker( self.local_author, &self.record_store, self.latest_broadcast, latest_senders, clock,);
         pms₀ = nsPaceMaker self₀
         ((pms₁ , pmActs ) , auxPMSOK) = updatePacemaker pms₀
                                            (nsLocalAuthor self₀)
                                            (nsRecordStoreState self₀)
                                            (nsLatestBroadcast self₀)
                                            latestSenders
                                            clock
                                            (auxNsValidRSS auxPreNS)

-- let mut actions = self.process_pacemaker_actions(pacemaker_actions, smr_context);
         -- Can't keep this organized as in paper, because can't do with & where here
         ((self₁ , (smrContext₁ , actions₀)) , auxPrf) = processPacemakerActions self₀ auxPreNS pmActs auxPMSOK smrContext₀

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

         smrContextFinal = smrContext₀
         actionsFinal = {!!}

    in
      (self₁ , (smrContextFinal , actionsFinal)) , auxPrf


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

  record GlobalSystemState : Set₁ where
    constructor gss
    field
      gssNodeStates  : Author → Maybe NodeState   -- Nothing for non-existent or unstarted authors
      gssSmrContexts : Author → SmrContext        -- Some default for non-existent or unstarted authors
      gssMessagePool : MessagePool

  open GlobalSystemState

  record AuxGlobalSystemState (gss : GlobalSystemState) : Set₁ where
    field
      auxGssValidNodeStates : ∀ (a : Author) → {ns : NodeState} → gssNodeStates gss a ≡ just ns → AuxValidNodeState ns

  open AuxGlobalSystemState

  initialGlobalState : GlobalSystemState
  initialGlobalState = {!!}
---------- Actions ---------

  processShouldNotifyLeader : Maybe Author → NodeState → MessagePool → MessagePool
  processShouldNotifyLeader nothing    _  mp = mp
  processShouldNotifyLeader (just ldr) ns mp = insert {nsLocalAuthor ns} {ldr} mp {!!}   -- TODO: Send DataSyncNotification to leader?

  processShouldBroadcast : Bool → NodeState → MessagePool → MessagePool
  processShouldBroadcast false _  mp = mp
  processShouldBroadcast true  ns mp = mp       -- TODO: Send DataSyncNotification to .. whom?  Containing what?
                                                   -- From p. 19: // Ask that we reshare the proposal. (proposed_block)
                                                   -- From p. 38  // Access the block proposed by the leader chosen by the Pacemaker (if any).

  processNodeUpdateActions : MessagePool → Author → NodeState → NodeUpdateActions → MessagePool
  processNodeUpdateActions mp₀ a ns (mkNodeUpdateAction ssu snl sb) =
    let mp₁ = processShouldNotifyLeader snl ns mp₀
        mp₂ = processShouldBroadcast    sb  ns mp₁
    in mp₂

---------- Actions and reachable states ----------

  effUpdateNode′ : Author
                 → (ns : NodeState)
                 → AuxValidNodeState ns
                 → SmrContext
                 → NodeUpdateActions
                 → (pre : GlobalSystemState)
                 → AuxGlobalSystemState pre
                 → Σ ( GlobalSystemState ) (λ post → AuxGlobalSystemState post)
  effUpdateNode′ a ns₁ validns₁ smr₁ nua pre auxPre =
                       let mp₀              = gssMessagePool pre
                           mp₁              = processNodeUpdateActions mp₀ a ns₁ nua
                           (nss₁ , nss₁prf) = (gssNodeStates pre)  [ a := (just ns₁)  , _≟ℕ_  ]
                           (smrs₁ , _)      = (gssSmrContexts pre) [ a := smr₁        , _≟ℕ_  ]
                           finalGss         = gss nss₁ smrs₁ mp₁
                           in finalGss ,
                             record { auxGssValidNodeStates =  λ a′ prf → postNSfor a′ a ns₁ validns₁ pre auxPre finalGss nss₁prf prf }
                               where postNSfor : (a′ a    : Author)
                                               → (ns₁     : NodeState)
                                               → AuxValidNodeState ns₁
                                               → (pre     : GlobalSystemState)
                                               → (auxPre  : AuxGlobalSystemState pre)
                                               → (post    : GlobalSystemState)
                                               → (nss₁prf : overrideProp (gssNodeStates pre) a (just ns₁) (gssNodeStates post) )
                                               → {ns      : NodeState}
                                               → (prf     : gssNodeStates post a′ ≡ just ns)
                                               → AuxValidNodeState ns
                                     postNSfor a′ a ns₁ validns₁ pre auxPre post nss₁prf {ns}
                                       with (gssNodeStates post) a′ | inspect (gssNodeStates post) a′
                                     ...| nothing  | _ = λ ()
                                     ...| just ns′ | Reveal[ nsprf ]

                                         -- TODO: consider reordering the two "with"s below; I think it will become simpler
                                         with a′ ≟ℕ a | nss₁prf a′
                                           -- The new NodeState we have assigned to a′ (because a′ ≡ a), is valid
                                     ...|  yes a′≡a | inj₁ xx2 = ⊥-elim ((proj₁ xx2) a′≡a)
                                     ...|  yes a′≡a | inj₂ xx2 rewrite a′≡a = λ prf → subst AuxValidNodeState
                                                                                            (just-injective prf)
                                                                                            (subst AuxValidNodeState
                                                                                                   (just-injective (trans (sym (proj₂ xx2)) nsprf))
                                                                                                   validns₁)
                                           -- If a′ ≢ a, then the auxilirary information about a′s NodeState is the same in the
                                           -- post state as in the pre state.
                                     ...|  no  xx | _ with nss₁prf a′
                                     ...|               inj₂ xx1 = ⊥-elim (xx (proj₁ xx1))
                                     ...|               inj₁ xx1 = λ prf → ((auxGssValidNodeStates auxPre) a′ {ns})
                                                                         (trans (trans (sym (proj₂ xx1)) nsprf) prf)

  effUpdateNode : Author
                → NodeTime
                → (pre : GlobalSystemState)
                → AuxGlobalSystemState pre
                → Σ ( GlobalSystemState ) (λ post → AuxGlobalSystemState post)
  effUpdateNode a nt pre auxPre
     with (gssNodeStates pre) a | inspect (gssNodeStates pre) a
  ...|  nothing   | _             = pre , auxPre
  ...|  (just ns) | Reveal[ prf ]
        with updateNode ns nt (gssSmrContexts pre a) (auxGssValidNodeStates auxPre a prf)
  ...|    (ns₁ , (smr₁ , nua)) , validns₁ = effUpdateNode′ a ns₁ validns₁ smr₁ nua pre auxPre

  -- Question: do we need an AuxGlobalSystemState?  Maybe when we get to liveness?
  data ReachableState : (gss : GlobalSystemState) → Set₁ where
    rchstEmpty      : ∀ {init : GlobalSystemState} → AuxGlobalSystemState init → ReachableState init
    rchstUpdateNode : ∀ {a : Author} {nt : NodeTime} {preState : GlobalSystemState} {auxPre : AuxGlobalSystemState preState}
                    → ReachableState preState
                    → ReachableState (proj₁ (effUpdateNode a nt preState auxPre))
    -- TODO: Allow bad guys to send whatever messages they want.  No need to model their state,
    -- because state only serves to constrain what messages honest guys send.

  reachableStateProperties : ∀ {gss : GlobalSystemState}
                           → ReachableState gss
                           → AuxGlobalSystemState gss
  reachableStateProperties {gs} (rchstEmpty {init} auxprf) = auxprf
  reachableStateProperties {gs} (rchstUpdateNode {a} {nt} {pre} {auxPre} rch′) = proj₂ (effUpdateNode a nt pre auxPre)


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
                            {m₁ m₂ : Message a {!!}}
                            {v₁ v₂ : Vote}
                            {s : GlobalSystemState}
                          → ReachableState s
                          → m₁ ∈mp gssMessagePool s
                          → m₂ ∈mp gssMessagePool s
                          → (V v₁) ∈msg m₁
                          → (V v₂) ∈msg m₂
                          → Vote.vEpoch v₁ ≡ Vote.vEpoch v₂
                          → Vote.vRound v₁   ≡ Vote.vRound v₂
                          → isHonestP ec a
                          → Vote.vBlockHash v₁ ≡ Vote.vBlockHash v₂
  honestVotesConsistent = {!!}
