open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

module LibraBFT.Concrete.RecordStoreState
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec : EpochConfig)
 where

  open import LibraBFT.Abstract.Records                                  ec 
  open import LibraBFT.Abstract.BFT                                      ec 
  open import LibraBFT.Abstract.Records.Extends             hash hash-cr ec 
  open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
  open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec
  import      LibraBFT.Abstract.RecordStoreState.Invariants hash hash-cr ec
    as AbstractI

  hashRecord : Record → Hash
  hashRecord = hash ∘ encodeR

  open import LibraBFT.Concrete.Util.HashSet hashRecord

  -- VCM: I'm simplifying this abruptly; we should only
  --      add fields here as needed
  record RecordStoreState : Set where
    constructor mkRecordStoreState
    field
      -- rssInitiaState       : State
      rssPool                 : HashSet
      rssCurrentRound         : Round
      -- rssCurrentVotes         : HashMap (Author ec) Vote
  open RecordStoreState

  _∈RSS_ : Record → RecordStoreState → Set
  (I _) ∈RSS rs = Unit -- The initial record is not really *in* the record store,
  (B x) ∈RSS rs = (B x) ∈HS (rssPool rs)
  (Q x) ∈RSS rs = (Q x) ∈HS (rssPool rs)

  _∈RSS?_ : (r : Record)(rss : RecordStoreState) → Dec (r ∈RSS rss)
  (I _) ∈RSS? rss = yes unit
  (B b) ∈RSS? rss = (B b) ∈HS? (rssPool rss)
  (Q b) ∈RSS? rss = (Q b) ∈HS? (rssPool rss)

{-
  ∈RSS-correct : (rss : RecordStoreState)(r : Record)
               → r ∈RSS rss → lookup (rssPool rss) (hashRecord r) ≡ just r
  ∈RSS-correct rss (B x) prf = lookup-correct (B x) (rssPool rss) prf
  ∈RSS-correct rss (Q x) prf = lookup-correct (Q x) (rssPool rss) prf

  ∈RSS-correct-⊥ : (rss : RecordStoreState)(r : Record)
                 → r ∈RSS rss → lookup (rssPool rss) (hashRecord r) ≡ nothing → ⊥
  ∈RSS-correct-⊥ = {!!}
-}


  ∈RSS-irrelevant : ∀{r rss}(p₀ p₁ : r ∈RSS rss) → p₀ ≡ p₁
  ∈RSS-irrelevant {I x} unit unit = refl
  ∈RSS-irrelevant {B x} {st} p0 p1     
    = ∈HS-irrelevant (B x) (rssPool st) p0 p1
  ∈RSS-irrelevant {Q x} {st} p0 p1    
    = ∈HS-irrelevant (Q x) (rssPool st) p0 p1

  instance
    abstractRSS : isRecordStoreState RecordStoreState
    abstractRSS = record
      { isInPool            = _∈RSS_
      ; isInPool-irrelevant = ∈RSS-irrelevant
      }

  --------------------
  -- The Invariants --
  --------------------

  Correct : RecordStoreState → Set
  Correct st = AbstractI.Correct st

  IncreasingRound : RecordStoreState → Set
  IncreasingRound st = AbstractI.IncreasingRoundRule st

  VotesOnlyOnce : RecordStoreState → Set
  VotesOnlyOnce st = AbstractI.VotesOnlyOnceRule st

  LockedRound : RecordStoreState → Set₁
  LockedRound st = AbstractI.LockedRoundRule st

  -- A Valid Record Store State is one where all
  -- the invariants are respected.
  record ValidRSS (rss : RecordStoreState) : Set₁ where
    constructor valid-rss
    field
      correct           : Correct rss
      incr-round-rule   : IncreasingRound rss
      votes-once-rule   : VotesOnlyOnce rss
      locked-round-rule : LockedRound rss

  ---------------------
  -- The Empty State --
  ---------------------

  emptyRSS : RecordStoreState
  emptyRSS = record {
     -- ; rssInitial              = init
       -- rssInitiaState   : State
       rssPool                 = empty
     ; rssCurrentRound         = 1
     -- ; rssCurrentVotes         = empty
    }

  -- And now this is really trivial
  emptyRSS-valid : ValidRSS emptyRSS
  emptyRSS-valid =
    valid-rss (λ { (I mkInitial) _  → WithRSS.empty
                 ; (B _) abs → ⊥-elim (∈HS-empty-⊥ abs) 
                 ; (Q _) abs → ⊥-elim (∈HS-empty-⊥ abs)})
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ _ _ (WithRSS.step _ _ {abs}) _ _ 
                 → ⊥-elim (∈HS-empty-⊥ abs) })

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecord : Set where
    B : BBlock NodeId → NetworkRecord
    Q : BQC    NodeId → NetworkRecord
    --- ...

  -- Employ structural checks on the records when receiving
  -- them on the wire.
  check-signature-and-format : Signed NetworkRecord → Maybe Record
  check-signature-and-format = {!!}

  --------------------------------
  -- Semantically Valid Records --

  -- A record extends some other in a state if there exists
  -- a record chain in said state that ends on the record supposed
  -- to be extended
  data Extends (rss : RecordStoreState) : Record → Set where
     -- VCM: We might carry more information on this constructor
     extends : ∀{r r'}
             → (rInPool : r ∈RSS rss)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties.
             → lookup (rssPool rss) (hashRecord r') ≡ nothing
             → r ← r'
             → Extends rss r'


{-
  -- MSM: Why is this needed?
  -- VCM: This is the function that should do all the checks and
  --      pass that through a proof object 'Extends'
  --      
  --
  -- 'Extends' must be a decidable; We decide whether a record
  -- exnteds the state by performing the necessary checks.
  -- We might need to pass in an 'ValidRSS rss' argument here
-}


  extends-Q? : (rss : RecordStoreState)(q : QC)
             → lookup (rssPool rss) (hashRecord (Q q)) ≡ nothing
             → Maybe (Extends rss (Q q)) 
  extends-Q? rss q ok = {!!}

  extends-B? : (rss : RecordStoreState)(b : Block)
             → lookup (rssPool rss) (hashRecord (B b)) ≡ nothing
             → Maybe (Extends rss (B b)) 
  extends-B? rss b ok 
  -- 1. Are we extending the initial record?
    with bPrevQCHash b ≟Hash hashRecord (I mkInitial)
  ...| yes refl with 1 ≤? (bRound b)
  ...| yes xx = just (extends {r = I mkInitial} unit ok
                                (I←B xx refl))
  ...| no _   = nothing
  extends-B? rss b ok
     | no  ¬Init
  -- 2. Ok, if not the initial, which one? We must look it up.
    with lookup (rssPool rss) (bPrevQCHash b)
       | inspect (lookup (rssPool rss)) (bPrevQCHash b)
  -- 2.1 case nothing was found, it does not extend.
  ...| nothing | [ R ] = nothing
  -- 2.2 case we found the initial contradicts the check at (1)
  ...| just (I mkInitial) | [ R ]
     = ⊥-elim (¬Init (lookup-correct' (bPrevQCHash b) (rssPool rss) R))
  -- 2.3 case we found a block, it does not extend. Blocks only extend QC's
  ...| just (B _) | [ R ] = nothing
  -- 2.4 case we found a QC, it might extend
  ...| just (Q q) | [ R ]
  -- 2.4.1 Is block round strictly greater than the QC it extends?
     with suc (qRound (qBase q)) ≤? bRound b
  -- 2.4.1.1 No; the rounds are not ok.
  ...| no round-nok = nothing
  -- 2.4.1.2 Yes, rounds are fine; So far, it extends.
  --         VCM: Shouldn't we perform additional checks?
  ...| yes round-ok = just (extends (lookup-correct'' _ _ R) ok
                             (Q←B {q} round-ok (sym (lookup-correct' _ _ R))))

  -- VCM: Looks like we will need some sort of DSL to
  -- be able to assemble this function in a reasonably readable way...
  extends? : (rss : RecordStoreState)(r : Record) → Maybe (Extends rss r)
  extends? rss r with (lookup (rssPool rss)) (hashRecord r) | inspect (lookup (rssPool rss)) (hashRecord r)
  ...| just _  | [ _ ] = nothing -- Cannot insert this record (either it is already in or there is a hash conflict)
  ...| nothing | [ ok ] with r 
  ...| I _ = nothing
  ...| B b = extends-B? rss b ok
  ...| Q q = extends-Q? rss q ok

  --------------------------
  -- Insertion of Records --

  insert : (rss : RecordStoreState)(r' : Record)(ext : Extends rss r')
         → RecordStoreState
  insert rss r' (extends _ nc _) = record rss 
     {rssPool = hs-insert (rssPool rss) r' nc
     }

  ---------------------
  -- IS CORRECT RULE --

  -- We can always inject a record chain from a recordstorestate
  -- into another by proving the later contains at least all the
  -- records of the former.
  RecordChain-grow
    : {rss rss' : RecordStoreState}{s : Record} 
    → (∀ {r} → r ∈RSS rss → r ∈RSS rss')
    → WithRSS.RecordChain rss s → WithRSS.RecordChain rss' s
  RecordChain-grow f WithRSS.empty           
    = WithRSS.empty
  RecordChain-grow f (WithRSS.step rc x {p}) 
    = WithRSS.step (RecordChain-grow f rc) x {f p}

  -- Inserting does not loose any records.
  insert-stable : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
                → {r : Record}
                → r ∈RSS rss
                → r ∈RSS (insert rss r' ext)
  insert-stable ext {I x} hyp = unit
  insert-stable (extends _ nc _) {B x} hyp = hs-insert-stable {prf = nc} hyp
  insert-stable (extends _ nc _) {Q x} hyp = hs-insert-stable {prf = nc} hyp

  -- If a record is not in store before insertion, but it is after
  -- the insertion, this record must have been the inserted one.
  insert-target : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
                → {r : Record}
                → ¬ (r ∈RSS rss)
                → r ∈RSS (insert rss r' ext)
                → r ≡ r'
  insert-target ext {I x} neg hyp = ⊥-elim (neg hyp)
  insert-target (extends _ nc _) {B x} neg hyp = hs-insert-target {prf = nc} neg hyp
  insert-target (extends _ nc _) {Q x} neg hyp = hs-insert-target {prf = nc} neg hyp

  -- Inserting a record is provably correct.
  insert-∈RSS : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
              → r' ∈RSS insert rss r' ext
  insert-∈RSS {rss}{I _}(extends _ nc _) = unit
  insert-∈RSS {rss}{B x}(extends _ nc _) = hs-insert-works (B x) (rssPool rss) nc
  insert-∈RSS {rss}{Q x}(extends _ nc _) = hs-insert-works (Q x) (rssPool rss) nc

  insert-ok-correct : (rss : RecordStoreState)(r' : Record)(ext : Extends rss r')
            → ValidRSS rss
            → Correct (insert rss r' ext)
  insert-ok-correct rss r' ext vrss s s∈post 
    with s ∈RSS? rss
  ...| yes s∈rss = RecordChain-grow (insert-stable ext) (ValidRSS.correct vrss s s∈rss)
  ...| no  s∉rss 
    rewrite insert-target ext s∉rss s∈post 
    with ext
  ...| extends {r = r} a b r←r'
     = WithRSS.step (RecordChain-grow (insert-stable {rss} (extends a b r←r')) (ValidRSS.correct vrss r a))
                    r←r' {insert-∈RSS (extends a b r←r')}

  ---------------------
  -- VOTES ONCE RULE --

  -- If we have two proofs that α voted in QC q; these proofs
  -- are the same. Here is where we need the IsSorted inside
  -- the qc! :)
  ∈QC-Vote-prop 
    : {α : Author ec}(q : QC) → (vα vα' : α ∈QC q) → vα ≡ vα'
  ∈QC-Vote-prop = {!!}

  data Dishonest (α : Author ec) : Set where
    same-order-diff-qcs 
      : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
      → q ≢ q'
      → vOrder (∈QC-Vote q vα) ≡ vOrder (∈QC-Vote q' vα')
      → Dishonest α

  postulate
    ACCOUNTABILITY-OPP : ∀{α} → Honest α → Dishonest α → ⊥

  insert-ok-votes-only-once : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → VotesOnlyOnce (insert rss r ext)
  insert-ok-votes-only-once rss r ext vrss α hα {q} {q'} q∈rss q'∈rss vα vα' ord 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈RSS? rss | (Q q') ∈RSS? rss
  -- 1.1 Yes, they are old. Easy! Rely on the hypothesis that the previous
  --     state was correct.
  ...| yes qOld | yes q'Old 
     = ValidRSS.votes-once-rule vrss α hα qOld q'Old vα vα' ord
  -- 1.2 No! One is old but the other is newly inserted. This must be impossible.
  --     We must add things to 'Extends' to be able to eliminate these two cases. 
  ...| no  qNew | yes q'Old 
     -- But wait. If q has been inserted but not q'; but at
     -- the same time we have a proof that q extends the state, 
     -- the rounds of the QC's must be different, which render
     -- the QC's different altogether. Hence, α is Dishonest and
     -- we have proof!
     = ⊥-elim (ACCOUNTABILITY-OPP hα 
                (same-order-diff-qcs {α} {q} {q'} vα vα' {!!} ord)) 
  ...| yes qOld | no  q'New = {!!}
  -- 1.3 Both QCs are new; hence must have been inserted
  --     now. This means that they must be equal; we rewrite on that and continue.
  ...| no  qNew | no  q'New 
    with trans (insert-target ext {Q q'} q'New q'∈rss) 
          (sym (insert-target ext {Q q} qNew q∈rss))
  ...| q≡q' rewrite Q-injective q≡q' 
                  | ∈QC-Vote-prop q vα vα' 
                  = refl

  insert-ok-increasing-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → IncreasingRound (insert rss r ext)
  insert-ok-increasing-round rss r ext vrss = {!!}

  insert-ok-locked-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → LockedRound (insert rss r ext)
  insert-ok-locked-round rss r ext vrss = {!!}

  insert-ok : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → ValidRSS (insert rss r ext)
  insert-ok rss r ext vrss =
    valid-rss
      (insert-ok-correct          rss r ext vrss)
      (insert-ok-increasing-round rss r ext vrss)
      (insert-ok-votes-only-once  rss r ext vrss)
      (insert-ok-locked-round     rss r ext vrss)
