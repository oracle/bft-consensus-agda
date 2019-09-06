-- Imports needed for defining module parameters

open import Data.Sum as Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality

open import Hash
open import Lemmas

module TestRecordStore
  -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is collision resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open WithCryptoHash hash hash-cr
  open import LibraBFT hash hash-cr

  -- Should (some of) these be reexported by LibraBFT?
  open import Data.Bool using (Bool; true; false)
  open import Data.Bool renaming (_≟_ to _≟Bool_) hiding (_<_)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Fin using (Fin ; fromℕ≤; toℕ)
  open import Data.Fin.Properties using (toℕ-injective) renaming (_≟_ to _≟Fin_)
  open import Data.List renaming (map to List-map)
  open import Data.List.Properties using (≡-dec)
  open import Data.List.Any
  open import Data.List.All
  open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
  open import Data.Nat.Properties
  open import Level using (0ℓ)
  open import Data.Maybe
  open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
  open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
  open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
  open import Data.Vec hiding (insert) renaming (lookup to lookupVec; allFin to allFinVec; map to mapVec; take to takeVec; tabulate to tabulateVec)
  open import Data.Vec.Bounded renaming (filter to filterVec) hiding ([] ; _∷_)
  open import Data.Vec.Relation.Unary.Any renaming (Any to AnyVec ; any to anyVec)
  open import Data.Vec.Relation.Unary.All renaming (All to AllVec ; all to allVec)
  open import Data.Vec.Properties
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_])
  open import Relation.Nullary using (Dec; yes; no; ¬_)
  open import Relation.Nullary.Negation using (contradiction; contraposition)
  open import Relation.Nullary.Negation using (contradiction; contraposition)

  open EpochConfiguration
  open NodeState
  open RecordStoreState

  init0 : Initial
  init0 = record { epochId = 1
                 ; seed    = 1
                 }
  hashInit0 : Hash
  hashInit0 = HashR (I init0)

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

  ec0 : EpochConfiguration
  ec0 = record {
          ecN                   = testN
        ; ecF                   = testF
        ; ecVotingRights        = dummyAuthors testN
        ; ecAux0<n              = 0<testN
        ; ecAux3f<n             = 3*testF<testN
        ; ecAuxVotersDistinct   = dummyAuthorsDistinct
        ; ecAuxGoodGuys         = dummyGoodGuys (testN ∸ testF) testF
        ; ecAuxGoodGuysDistinct = dummyGoodGuysDistinct
        }

  _ : lookupVec (ecVotingRights ec0) (Data.Fin.fromℕ≤ (s≤s z≤n))                   ≡ dummyAuthor 0
  _ = refl

  _ : lookupVec (ecVotingRights ec0) (Data.Fin.fromℕ≤ (s≤s (s≤s z≤n)))             ≡ dummyAuthor 1
  _ = refl

  _ : lookupVec (ecVotingRights ec0) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s z≤n))))       ≡ dummyAuthor 2
  _ = refl

  _ : lookupVec (ecVotingRights ec0) (Data.Fin.fromℕ≤ (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ dummyAuthor 3
  _ = refl

  _ : isVoter ec0 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isVoter ec0 (dummyAuthor 3) ≡ true
  _ = refl

  _ : isVoter ec0 (dummyAuthor 5) ≡ false
  _ = refl

  _ : isHonest ec0 (dummyAuthor 0) ≡ true
  _ = refl

  _ : isHonest ec0 (dummyAuthor 1) ≡ true
  _ = refl

  _ : isHonest ec0 (dummyAuthor 2) ≡ true
  _ = refl

  _ : isHonest ec0 (dummyAuthor 3) ≡ false
  _ = refl

  _ : isHonest ec0 (dummyAuthor 5) ≡ false
  _ = refl

------------------------- End test data ----------------------


-------------------- RecordStoreState tests --------------------

  rss0 : RecordStoreState
  rss0 = emptyRSS 1 ec0 init0

  arss0 : AuxRecordStoreState rss0
  arss0 = record { auxRssLemma1-1 = λ {r} {isCR} x →
                                   contradiction x (emptyIsEmpty r
                                                                 (rssEpochId rss0)
                                                                 (rssConfiguration rss0)
                                                                 (rssInitial rss0))
          }

  block0 : Block
  block0 = record { round = 1
                  ; prevQCHash = HashR (I init0)
                  ; author = dummyAuthor 42
                  }

  bl0 : mkBlock (hash (encodeR (I init0))) 1 42 ≡ block0
  bl0 = refl

  hh : Hash
  hh = HashR (R (B block0))

  mt : Hash → Maybe Block
  mt = emptyHM {Hash} {Block}

  _ : mt hh ≡ nothing
  _ = refl

  ---- A few silly properties I proved for practice, keeping them here for now

  yy1 : ∀ (x : List Bool) → (Data.List.Properties.≡-dec _≟Bool_ x x) ≡ yes refl
  yy1 [] = refl
  yy1 (h ∷ t) with h ≟Bool h | Data.List.Properties.≡-dec _≟Bool_ t t
  ...| no h≢h | _      = ⊥-elim (h≢h refl)
  ...| yes _  | no t≢t = ⊥-elim (t≢t refl)
  ...| yes xx | yes xx1 rewrite xx | xx1 = refl

  yyy : (overrideFn {Level.zero} {Level.zero} {Hash} {Maybe Block} mt hh (just block0)  _≟Hash_) hh ≡ just block0
  yyy with hh ≟Hash hh
  ...| yes xx rewrite xx = refl
  ...| no  xx = ⊥-elim (xx refl)

  zzz : (emptyHM [ (HashR (R (B block0))) := (just block0) , _≟Hash_ ]) (HashR (R (B block0))) ≡ just block0
  zzz with (HashR (R (B block0))) ≟Hash (HashR (R (B block0)))
  ...| yes xx rewrite xx = refl
  ...| no  xx = ⊥-elim (xx refl)

  rss1 : RecordStoreState
  rss1 = rssInsert (B block0) rss0

  arss1 : AuxRecordStoreState rss1
  arss1 = record {
            auxRssLemma1-1 = λ {r} {isCR} x → hᵢ←⋆R {r = r} {isCR = isCR} x
          }

  -- TODO : Add tests showing we can also add Blocks that depend on QCs, and we can add QCs and
  -- Votes and still preserve lemma 1-1

  ns0 : NodeState
  ns0 = mkNodeState rss0 pm0 0 (dummyAuthor 42) 0 0

  proposeBlock0 : Block
  proposeBlock0 = proj₁ (proposeBlock ns0 (dummyAuthor 42) (hashInit0) 0 0)

  proposeBlock0≡block0 : block0 ≡ proposeBlock0
  proposeBlock0≡block0 = refl

  block0Valid : Valid (B block0) rss0
  block0Valid = B block0 rss0 (inj₂ ⟨ I←B refl , s≤s z≤n ⟩)

