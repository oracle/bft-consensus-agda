{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.BlockTree
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

  record BlockTree : Set where
    constructor mkBlockTree
    field
      btIdToBlock                 : HashSet
      -- btIdToQuorumCert         : HashSet
  open BlockTree

  _∈BT_ : Record → BlockTree → Set
  (I _) ∈BT rs = Unit -- The initial record is not really *in* the record store,
  (B x) ∈BT rs = (B x) ∈HS (btIdToBlock rs)
  (Q x) ∈BT rs = (Q x) ∈HS (btIdToBlock rs)

  _∈BT?_ : (r : Record)(bt : BlockTree) → Dec (r ∈BT bt)
  (I _) ∈BT? bt = yes unit
  (B b) ∈BT? bt = (B b) ∈HS? (btIdToBlock bt)
  (Q b) ∈BT? bt = (Q b) ∈HS? (btIdToBlock bt)

{-
  ∈BT-correct : (bt : BlockTree)(r : Record)
               → r ∈BT bt → lookup (btIdToBlock bt) (hashRecord r) ≡ just r
  ∈BT-correct bt (B x) prf = lookup-correct (B x) (btIdToBlock bt) prf
  ∈BT-correct bt (Q x) prf = lookup-correct (Q x) (btIdToBlock bt) prf

  ∈BT-correct-⊥ : (bt : BlockTree)(r : Record)
                 → r ∈BT bt → lookup (btIdToBlock bt) (hashRecord r) ≡ nothing → ⊥
  ∈BT-correct-⊥ = {!!}
-}


  ∈BT-irrelevant : ∀{r bt}(p₀ p₁ : r ∈BT bt) → p₀ ≡ p₁
  ∈BT-irrelevant {I x} unit unit = refl
  ∈BT-irrelevant {B x} {st} p0 p1     
    = ∈HS-irrelevant (B x) (btIdToBlock st) p0 p1
  ∈BT-irrelevant {Q x} {st} p0 p1    
    = ∈HS-irrelevant (Q x) (btIdToBlock st) p0 p1

  instance
    abstractRSS : isRecordStoreState BlockTree
    abstractRSS = record
      { isInPool            = _∈BT_
      ; isInPool-irrelevant = ∈BT-irrelevant
      }

  --------------------
  -- The Invariants --
  --------------------

  Correct : BlockTree → Set
  Correct st = AbstractI.Correct st

  IncreasingRound : BlockTree → Set
  IncreasingRound st = AbstractI.IncreasingRoundRule st

  VotesOnlyOnce : BlockTree → Set
  VotesOnlyOnce st = AbstractI.VotesOnlyOnceRule st

  LockedRound : BlockTree → Set₁
  LockedRound st = AbstractI.LockedRoundRule st

  -- A Valid Record Store State is one where all
  -- the invariants are respected.
  record ValidBT (bt : BlockTree) : Set₁ where
    constructor valid-bt
    field
      correct           : Correct bt
      incr-round-rule   : IncreasingRound bt
      votes-once-rule   : VotesOnlyOnce bt
      locked-round-rule : LockedRound bt

  ---------------------
  -- The Empty State --
  ---------------------

  emptyBT : BlockTree
  emptyBT = record {
       btIdToBlock                 = empty
    }

  -- And now this is really trivial
  emptyBT-valid : ValidBT emptyBT
  emptyBT-valid =
    valid-bt (λ { (I mkInitial) _  → WithRSS.empty
                 ; (B _) abs → ⊥-elim (∈HS-empty-⊥ abs) 
                 ; (Q _) abs → ⊥-elim (∈HS-empty-⊥ abs)})
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ _ _ (WithRSS.step _ _ {abs}) _ _ 
                 → ⊥-elim (∈HS-empty-⊥ abs) })

  --------------------------------
  -- Semantically Valid Records --

  -- A record extends some other in a state if there exists
  -- a record chain in said state that ends on the record supposed
  -- to be extended
  data Extends (bt : BlockTree) : Record → Set where
     -- VCM: We might carry more information on this constructor
     extends : ∀{r r'}
             → (rInPool : r ∈BT bt)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties.
             → (r'New : lookup (btIdToBlock bt) (hashRecord r') ≡ nothing)
             → r ← r'
             → Extends bt r'

  extends-Q? : (bt : BlockTree)(q : QC)
             → lookup (btIdToBlock bt) (hashRecord (Q q)) ≡ nothing
             → Maybe (Extends bt (Q q))
  extends-Q? bt q ok
    -- Structure is similar to extends-B? below, which is commented in detail.
    with lookup (btIdToBlock bt) (getPrevHash q)
       | inspect (lookup (btIdToBlock bt)) (getPrevHash q)
  ...| nothing    | [ _ ] = nothing
  ...| just (I _) | [ _ ] = nothing
  ...| just (Q _) | [ _ ] = nothing
  ...| just (B b) | [ R ]
     with getRound q ≟ getRound b
  ...| no _ = nothing
  ...| yes round-ok = just (extends (lookup-∈HS _ _ R) ok
                             (B←Q {b} round-ok (sym (lookup-correct _ _ R))))

  extends-B? : (bt : BlockTree)(b : Block)
             → lookup (btIdToBlock bt) (hashRecord (B b)) ≡ nothing
             → Maybe (Extends bt (B b))
  extends-B? bt b ok
  -- 1. Are we extending the initial record?
    with getPrevHash b ≟Hash hashRecord (I mkInitial)
  ...| yes refl with 1 ≤? getRound b
  ...| yes xx = just (extends {r = I mkInitial} unit ok
                                (I←B xx refl))
  ...| no _   = nothing
  extends-B? bt b ok
     | no  ¬Init
  -- 2. Ok, if not the initial, which one? We must look it up.
    with lookup (btIdToBlock bt) (getPrevHash b)
       | inspect (lookup (btIdToBlock bt)) (getPrevHash b)
  -- 2.1 case nothing was found, it does not extend.
  ...| nothing | [ R ] = nothing
  -- 2.2 case we found the initial contradicts the check at (1)
  ...| just (I mkInitial) | [ R ]
     = ⊥-elim (¬Init (lookup-correct (getPrevHash b) (btIdToBlock bt) R))
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
  -- We could level-up by making this a Dec (Extends bt r), showing that we can construct an
  -- Extends bt r or there isn't one, thus eliminating this "triviality" concern.
  extends? : (bt : BlockTree)(r : Record) → Maybe (Extends bt r)
  extends? bt r with (lookup (btIdToBlock bt)) (hashRecord r) | inspect (lookup (btIdToBlock bt)) (hashRecord r)
  ...| just _  | [ _ ] = nothing -- Cannot insert this record (either it is already in or there is a hash conflict)
  ...| nothing | [ ok ] with r 
  ...| I _ = nothing
  ...| B b = extends-B? bt b ok
  ...| Q q = extends-Q? bt q ok

  --------------------------
  -- Insertion of Records --

  insert : (bt : BlockTree)(r' : Record)(ext : Extends bt r')
         → BlockTree
  insert bt r' (extends _ nc _) = record bt 
     {btIdToBlock = hs-insert  r' (btIdToBlock bt) nc
     }

  ---------------------
  -- IS CORRECT RULE --

  -- We can always inject a record chain from a recordstorestate
  -- into another by proving the later contains at least all the
  -- records of the former.
  RecordChain-grow
    : {bt bt' : BlockTree}{s : Record} 
    → (∀ {r} → r ∈BT bt → r ∈BT bt')
    → WithRSS.RecordChain bt s → WithRSS.RecordChain bt' s
  RecordChain-grow f WithRSS.empty           
    = WithRSS.empty
  RecordChain-grow f (WithRSS.step rc x {p}) 
    = WithRSS.step (RecordChain-grow f rc) x {f p}

  -- Inserting does not loose any records.
  insert-stable : {bt : BlockTree}{r' : Record}(ext : Extends bt r')
                → {r : Record}
                → r ∈BT bt
                → r ∈BT (insert bt r' ext)
  insert-stable ext {I x} hyp = unit
  insert-stable (extends _ nc _) {B x} hyp = hs-insert-stable nc hyp
  insert-stable (extends _ nc _) {Q x} hyp = hs-insert-stable nc hyp

  -- If a record is not in store before insertion, but it is after
  -- the insertion, this record must have been the inserted one.
  insert-target : {bt : BlockTree}{r' : Record}(ext : Extends bt r')
                → {r : Record}
                → ¬ (r ∈BT bt)
                → r ∈BT (insert bt r' ext)
                → r ≡ r'
  insert-target ext {I x} neg hyp = ⊥-elim (neg hyp)
  insert-target (extends _ nc _) {B x} neg hyp = hs-insert-target nc neg hyp
  insert-target (extends _ nc _) {Q x} neg hyp = hs-insert-target nc neg hyp

  -- Inserting a record is provably correct.
  insert-∈BT : {bt : BlockTree}{r' : Record}(ext : Extends bt r')
              → r' ∈BT insert bt r' ext
  insert-∈BT {bt}{I _}(extends _ nc _) = unit
  insert-∈BT {bt}{B x}(extends _ nc _) = hs-insert-∈HS (B x) (btIdToBlock bt) nc
  insert-∈BT {bt}{Q x}(extends _ nc _) = hs-insert-∈HS (Q x) (btIdToBlock bt) nc

  insert-ok-correct : (bt : BlockTree)(r' : Record)(ext : Extends bt r')
            → ValidBT bt
            → Correct (insert bt r' ext)
  insert-ok-correct bt r' ext vbt s s∈post 
    with s ∈BT? bt
  ...| yes s∈bt = RecordChain-grow (insert-stable ext) (ValidBT.correct vbt s s∈bt)
  ...| no  s∉bt 
    rewrite insert-target ext s∉bt s∈post 
    with ext
  ...| extends {r = r} a b r←r' 
     = WithRSS.step (RecordChain-grow (insert-stable {bt} (extends a b r←r')) 
                                      (ValidBT.correct vbt r a))
                    r←r' {insert-∈BT (extends a b r←r')}

  ---------------------
  -- VOTES ONCE RULE --

  -- If we have two proofs that α voted in QC q; these proofs
  -- are the same. Here is where we will need the IsSorted inside
  -- the qc! :)
  ∈QC-Vote-prop 
    : {α : Author ec}(q : QC) → (vα vα' : α ∈QC q) → vα ≡ vα'
  ∈QC-Vote-prop = {!!}

  insert-ok-votes-only-once : (bt : BlockTree)(r : Record)(ext : Extends bt r)
            → ValidBT bt
            → VotesOnlyOnce (insert bt r ext)
  insert-ok-votes-only-once bt r ext vbt α hα {q} {q'} q∈bt q'∈bt vα vα' ord 
  -- 0. Are the QCs equal?
    with q ≟QC q'
  ...| yes refl rewrite ∈QC-Vote-prop q vα vα' = refl
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈BT? bt | (Q q') ∈BT? bt
  -- 1.1 Yes, they are old. Easy! Rely on the hypothesis that the previous
  --     state was correct.
  ...| yes qOld | yes q'Old 
     = ValidBT.votes-once-rule vbt α hα qOld q'Old vα vα' ord
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
    with trans (insert-target ext {Q q'} q'New q'∈bt) 
          (sym (insert-target ext {Q q} qNew q∈bt))
  ...| q≡q' = ⊥-elim (q≢q' (sym (Q-injective q≡q')))

  insert-ok-increasing-round : (bt : BlockTree)(r : Record)(ext : Extends bt r)
            → ValidBT bt
            → IncreasingRound (insert bt r ext)
  insert-ok-increasing-round bt r ext vbt α hα {q} {q'} q∈bt q'∈bt va va' ord 
  -- 0. Are the QCs equal? Well, no, the orders are different
    with q ≟QC q'
  ...| yes refl = {!!} -- impossible!
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈BT? bt | (Q q') ∈BT? bt
  -- 1.1. Both are old; simple. Use hypothesis
  ...| yes qOld | yes q'Old 
     = ValidBT.incr-round-rule vbt α hα qOld q'Old va va' ord
  -- 1.2. Both are new, impossible; we just saw they must be different.
  ...| no  qNew | no  q'New 
     = ⊥-elim (q≢q' (sym (Q-injective 
          (trans (insert-target ext {Q q'} q'New q'∈bt) 
          (sym (insert-target ext {Q q} qNew q∈bt))))))
  ...| yes qOld | no  q'New = {!!}
  ...| no  qNew | yes q'Old = {!!}


  insert-ok-locked-round : (bt : BlockTree)(r : Record)(ext : Extends bt r)
            → ValidBT bt
            → LockedRound (insert bt r ext)
  insert-ok-locked-round bt r ext vbt = {!!}

  insert-ok : (bt : BlockTree)(r : Record)(ext : Extends bt r)
            → ValidBT bt
            → ValidBT (insert bt r ext)
  insert-ok bt r ext vbt =
    valid-bt
      (insert-ok-correct          bt r ext vbt)
      (insert-ok-increasing-round bt r ext vbt)
      (insert-ok-votes-only-once  bt r ext vbt)
      (insert-ok-locked-round     bt r ext vbt)
