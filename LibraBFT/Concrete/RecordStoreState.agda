{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.NetworkRecords

module LibraBFT.Concrete.RecordStoreState
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec : EpochConfig)
 where

  open import LibraBFT.Abstract.Records                                  ec 
  open import LibraBFT.Abstract.Rules                                    ec
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

  data VerNetworkRecord : Set where
    B : (vs : VerSigned (BBlock (Author ec)))
      → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
      → VerNetworkRecord
    V : (vs : VerSigned (BVote (Author ec)))
      → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
      → VerNetworkRecord
    C : (vs : VerSigned (BC (Author ec)))
      → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
      → VerNetworkRecord
    -- ... TOFINISH

  -- Employ structural checks on the records when receiving them on the wire.
  check-signature-and-format : NetworkRecord → Maybe VerNetworkRecord
  check-signature-and-format (V nv) 
  -- Is the author of the vote an actual author?
    with isAuthor ec (vAuthor (content nv)) 
  -- 1; No! Reject!
  ...| nothing = nothing
  -- 2; Yes! Now we must check whether the signature matches
  ...| just α  
    with checkSignature-prf (pkAuthor ec α) (Signed-map (BVote-map (λ _ → α)) nv)
  ...| nothing = nothing
  ...| just (va , prf1 , refl) = just (V va prf1)

  check-signature-and-format (B nb) = {!!}
  check-signature-and-format (Q nq) = {!!}
  check-signature-and-format (C nc) = {!!}

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
             → (r'New : lookup (rssPool rss) (hashRecord r') ≡ nothing)
             → r ← r'
             → Extends rss r'

  extends-Q? : (rss : RecordStoreState)(q : QC)
             → lookup (rssPool rss) (hashRecord (Q q)) ≡ nothing
             → Maybe (Extends rss (Q q))
  extends-Q? rss q ok
    -- Structure is similar to extends-B? below, which is commented in detail.
    with lookup (rssPool rss) (getPrevHash q)
       | inspect (lookup (rssPool rss)) (getPrevHash q)
  ...| nothing    | [ _ ] = nothing
  ...| just (I _) | [ _ ] = nothing
  ...| just (Q _) | [ _ ] = nothing
  ...| just (B b) | [ R ]
     with getRound q ≟ getRound b
  ...| no _ = nothing
  ...| yes round-ok = just (extends (lookup-∈HS _ _ R) ok
                             (B←Q {b} round-ok (sym (lookup-correct _ _ R))))

  extends-B? : (rss : RecordStoreState)(b : Block)
             → lookup (rssPool rss) (hashRecord (B b)) ≡ nothing
             → Maybe (Extends rss (B b))
  extends-B? rss b ok
  -- 1. Are we extending the initial record?
    with getPrevHash b ≟Hash hashRecord (I mkInitial)
  ...| yes refl with 1 ≤? getRound b
  ...| yes xx = just (extends {r = I mkInitial} unit ok
                                (I←B xx refl))
  ...| no _   = nothing
  extends-B? rss b ok
     | no  ¬Init
  -- 2. Ok, if not the initial, which one? We must look it up.
    with lookup (rssPool rss) (getPrevHash b)
       | inspect (lookup (rssPool rss)) (getPrevHash b)
  -- 2.1 case nothing was found, it does not extend.
  ...| nothing | [ R ] = nothing
  -- 2.2 case we found the initial contradicts the check at (1)
  ...| just (I mkInitial) | [ R ]
     = ⊥-elim (¬Init (lookup-correct (getPrevHash b) (rssPool rss) R))
  -- 2.3 case we found a block, it does not extend. Blocks only extend QC's
  ...| just (B _) | [ R ] = nothing
  -- 2.4 case we found a QC, it might extend
  ...| just (Q q) | [ R ]
  -- 2.4.1 Is block round strictly greater than the QC it extends?
     with suc (getRound q) ≤? getRound b
  -- 2.4.1.1 No; the rounds are not ok.
  ...| no round-nok = nothing
  -- 2.4.1.2 Yes, rounds are fine; So far, it extends.
  --         VCM: Shouldn't we perform additional checks?
  ...| yes round-ok = just (extends (lookup-∈HS _ _ R) ok
                             (Q←B {q} round-ok (sym (lookup-correct _ _ R))))

  -- This shows how we can construct an Extends record, as the concrete model will need to do.
  -- However, it only produces a Maybe Extends, wnich could be satisfied by alway returning nothing.
  -- We could level-up by making this a Dec (Extends rss r), showing that we can construct an
  -- Extends rss r or there isn't one, thus eliminating this "triviality" concern.
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
     {rssPool = hs-insert  r' (rssPool rss) nc
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
  insert-stable (extends _ nc _) {B x} hyp = hs-insert-stable nc hyp
  insert-stable (extends _ nc _) {Q x} hyp = hs-insert-stable nc hyp

  -- If a record is not in store before insertion, but it is after
  -- the insertion, this record must have been the inserted one.
  insert-target : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
                → {r : Record}
                → ¬ (r ∈RSS rss)
                → r ∈RSS (insert rss r' ext)
                → r ≡ r'
  insert-target ext {I x} neg hyp = ⊥-elim (neg hyp)
  insert-target (extends _ nc _) {B x} neg hyp = hs-insert-target nc neg hyp
  insert-target (extends _ nc _) {Q x} neg hyp = hs-insert-target nc neg hyp

  -- Inserting a record is provably correct.
  insert-∈RSS : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
              → r' ∈RSS insert rss r' ext
  insert-∈RSS {rss}{I _}(extends _ nc _) = unit
  insert-∈RSS {rss}{B x}(extends _ nc _) = hs-insert-∈HS (B x) (rssPool rss) nc
  insert-∈RSS {rss}{Q x}(extends _ nc _) = hs-insert-∈HS (Q x) (rssPool rss) nc

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
     = WithRSS.step (RecordChain-grow (insert-stable {rss} (extends a b r←r')) 
                                      (ValidRSS.correct vrss r a))
                    r←r' {insert-∈RSS (extends a b r←r')}

  ---------------------
  -- VOTES ONCE RULE --

  -- If we have two proofs that α voted in QC q; these proofs
  -- are the same. Here is where we will need the IsSorted inside
  -- the qc! :)
  ∈QC-Vote-prop 
    : {α : Author ec}(q : QC) → (vα vα' : α ∈QC q) → vα ≡ vα'
  ∈QC-Vote-prop = {!!}

  insert-ok-votes-only-once : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → VotesOnlyOnce (insert rss r ext)
  insert-ok-votes-only-once rss r ext vrss α hα {q} {q'} q∈rss q'∈rss vα vα' ord 
  -- 0. Are the QCs equal?
    with q ≟QC q'
  ...| yes refl rewrite ∈QC-Vote-prop q vα vα' = refl
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈RSS? rss | (Q q') ∈RSS? rss
  -- 1.1 Yes, they are old. Easy! Rely on the hypothesis that the previous
  --     state was correct.
  ...| yes qOld | yes q'Old 
     = ValidRSS.votes-once-rule vrss α hα qOld q'Old vα vα' ord
  -- 1.2 No! One is old but the other is newly inserted. This must be impossible.
  ...| no  qNew | yes q'Old 
     = {!!}  -- TODO: Previous proof for this case and the next used same-order-diff-qcs to "prove" that
             --       an author whose vote is included in two different QCs is dishonest, but this is not
             --       correct; it is the author of (at least) one of the QCs that is dishonest.
  ...| yes qOld | no  q'New 
     = {!!}
  -- 1.3 Both QCs are new; hence must have been inserted
  --     now. This means that they must be equal; Yet, we have
  --     just compared them before and found out they are not equal.
  ...| no  qNew | no  q'New 
    with trans (insert-target ext {Q q'} q'New q'∈rss) 
          (sym (insert-target ext {Q q} qNew q∈rss))
  ...| q≡q' = ⊥-elim (q≢q' (sym (Q-injective q≡q')))

  insert-ok-increasing-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → IncreasingRound (insert rss r ext)
  insert-ok-increasing-round rss r ext vrss α hα {q} {q'} q∈rss q'∈rss va va' ord 
  -- 0. Are the QCs equal? Well, no, the orders are different
    with q ≟QC q'
  ...| yes refl = {!!} -- impossible!
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈RSS? rss | (Q q') ∈RSS? rss
  -- 1.1. Both are old; simple. Use hypothesis
  ...| yes qOld | yes q'Old 
     = ValidRSS.incr-round-rule vrss α hα qOld q'Old va va' ord
  -- 1.2. Both are new, impossible; we just saw they must be different.
  ...| no  qNew | no  q'New 
     = ⊥-elim (q≢q' (sym (Q-injective 
          (trans (insert-target ext {Q q'} q'New q'∈rss) 
          (sym (insert-target ext {Q q} qNew q∈rss))))))
  ...| yes qOld | no  q'New = {!!}
  ...| no  qNew | yes q'Old = {!!}


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
