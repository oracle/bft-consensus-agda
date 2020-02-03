{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Concrete.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.BlockTree
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 
    -- We also need authorship and PKI information
    (ec  : EpochConfig)
    (pki : PKI)
    (CMD : Set) -- VCM: To be substituted by the command type
                -- of an abstract state machine.
 where

  open import LibraBFT.Concrete.Util.KVMap
  open import LibraBFT.Concrete.Records pki
  import LibraBFT.Concrete.Records.Valid ec pki as Meta

  
  record BlockTree : Set where
    constructor mkBlockTree
    field
      btIdToBlock      : KVMap Hash (Block CMD)
      -- VCM-QUESTION: The easiest solution seems to be conservatively 
      -- inserting all QCs that arrives to us in btIdToQuorumCert;
      -- If the QC comes in a standalone fashion, we add it.
      -- Id the QC comes in a block, we also add it.
      -- This means the _∈BT_ stays simple.
      btIdToQuorumCert : KVMap Hash (Σ QuorumCert Meta.IsValidQC)
  open BlockTree public

  --------------------------------
  -- Abstracting Blocks and QCs --
  --------------------------------

  -- Blocks and QCs are identified by hashes. In particular;
  -- Blocks are identified by their hash and QCs are identified
  -- by the hash of the block they certify.
  --
  -- This really means that two QCs that certify the same block
  -- are (by definition!!) the same. We capture this in the
  -- abstract model by using the _≈Rec_ relation.
  UID :  Set
  UID = Hash

  _≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁)
  _≟UID_ = _≟Hash_

  import LibraBFT.Abstract.Records ec UID _≟UID_ as Abs

  α-Block : Block CMD → Abs.Block
  α-Block b with bdBlockType (bBlockData b)
  ...| NilBlock = record
       { bId     = bId b 
       ; bPrevQC = just (biId (vdParent (qcVoteData (bdQuorumCert (bBlockData b)))))
       ; bRound  = bdRound (bBlockData b)
       }
  ...| Genesis = record
       { bId     = bId b 
       ; bPrevQC = nothing
       ; bRound  = bdRound (bBlockData b)
       }
  ...| Proposal cmd α = record
       { bId     = bId b 
       ; bPrevQC = just (biId (vdParent (qcVoteData (bdQuorumCert (bBlockData b)))))
       ; bRound  = bdRound (bBlockData b)
       }

  α-Vote : (qc : QuorumCert)(valid : Meta.IsValidQC qc) 
         → ∀ {as}
         → as ∈ qcVotes qc
         → Abs.Vote
  α-Vote qc v {author , sig} as∈QC = record
    { vAuthor   = Meta.ivaIdx (All-lookup (Meta.ivqcValidAuthors v) as∈QC)
    ; vBlockUID = biId (vdProposed (qcVoteData qc))
    ; vRound    = biRound (vdProposed (qcVoteData qc))
    ; vOrder    = {!!} -- VCM: here's the cliff hanger!
    }

  α-QC : Σ QuorumCert Meta.IsValidQC → Abs.QC
  α-QC (qc , valid) = record
    { qCertBlockId = biId (vdProposed (qcVoteData qc)) 
    ; qRound       = biRound (vdProposed (qcVoteData qc))
    ; qVotes       = All-reduce (α-Vote qc valid) (All-tabulate (λ x → x))
    ; qVotes-C1    = {!!} -- this proofs will come from the KV-store module
    ; qVotes-C2    = subst (_ ≤_) {!!} (Meta.ivqcSizeOk valid)
    ; qVotes-C3    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
    ; qVotes-C4    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self 
    }

  -- QC Facts
  --
  -- 1) Can a QC be in btIdToBlock but not in btIdToQuorumCert?
  -- NO! :)
  --
  -- 2) i) Say a leader sends (Proposal "transaction 1" (QC for parent: [v0, v1, v2])); timeouts.
  --   ii) Next leader sends (Proposal "transaction x" (QC for parent: [v1 ,v2 ,v3]));

  -- QC route:
  --
  -- leader rcv votes; create QC; put it in their own btIdToQC; send in the
  -- next block proposal; but also sends as SyncInfo!
  --
  -- when nodes rcv proposal; they first verify sync info. If it does verify
  -- populate btIdToQC then goes on to process the block.
  -- 

  -----------------------------------
  -- Interfacing with the Abstract --
  -----------------------------------

  -- VCM: The abstract model doesn't care too much for 
  -- how we decide to represent our concrete data. All we
  -- need is a way of proving some abstract piece of data belongs
  -- in the concrete storage. We will be using block hashes for that.
  -- A block is identified by its own block hash, a QC is
  -- identified by the hash of the block it verifies.

  open import LibraBFT.Abstract.Records.Extends        ec UID _≟UID_ 
  open import LibraBFT.Abstract.RecordStoreState       ec UID _≟UID_ 
  open import LibraBFT.Abstract.RecordChain            ec UID _≟UID_
  import LibraBFT.Abstract.RecordStoreState.Invariants ec UID _≟UID_
    as AbstractI
 
  -- VCM: We really need to invoke the abstraction function here; otherwise
  -- we have no guarantee that the rest of the fields of the abstract block
  -- are correct. This is what ensures the abstract model will not conjure blocks
  -- out of nowhere.

  _∈BT_ : Abs.Record → BlockTree → Set
  Abs.I     ∈BT bt = Unit -- The initial record is not really *in* the record store,
  (Abs.B b) ∈BT bt 
    = α-Block <M$> (lookup (Abs.bId b) (btIdToBlock bt)) ≡ just b
  (Abs.Q q) ∈BT bt 
    -- A qc is said to be in the abstract state iff there exists
    -- a qc that certifies the same block (i.e., with the same id).
    -- We don't particularly care for the list of votes or who authored it
    = (qcCertifies ∘ proj₁) <M$> (lookup (Abs.qCertBlockId q) (btIdToQuorumCert bt)) 
      ≡ just (Abs.qCertBlockId q)

  _∈BT?_ : (r : Abs.Record)(bt : BlockTree) → Dec (r ∈BT bt)
  Abs.I     ∈BT? bt = yes unit
  (Abs.B b) ∈BT? bt 
    with lookup (Abs.bId b) (btIdToBlock bt)
  ...| nothing = no (λ x → maybe-⊥ refl (sym x))
  ...| just r  
    with α-Block r Abs.≟Block b
  ...| yes refl = yes refl
  ...| no  ok   = no (ok ∘ just-injective)
  (Abs.Q q) ∈BT? bt = {!!}

  ∈BT-irrelevant : ∀{r rss}(p₀ p₁ : r ∈BT rss) → p₀ ≡ p₁
  ∈BT-irrelevant {Abs.I} unit unit    = refl
  ∈BT-irrelevant {Abs.B x} {st} p0 p1 = ≡-irrelevant p0 p1
  ∈BT-irrelevant {Abs.Q x} {st} p0 p1 = ≡-irrelevant p0 p1

  instance
    abstractBT : isRecordStoreState BlockTree
    abstractBT = record
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
  emptyBT = record 
    { btIdToBlock      = empty
    ; btIdToQuorumCert = empty
    }

{-

  -- This works for the B case of Correctness below, but need to simplify/generalize
  -- ⊥-elim (maybe-⊥ abs (subst ((_≡ nothing) ∘ (α-Block <M$>_)) (sym (kvm-empty {k = Abs.bId b})) (<M$>-nothing {a = 0ℓ}{f = α-Block})))

  -- And now this is really trivial
  emptyBT-valid : ValidBT emptyBT
  emptyBT-valid =
    valid-bt (λ { Abs.I _  → WithRSS.empty
                 ; (Abs.B _) abs → ⊥-elim (∈KV-empty-⊥ abs) 
                 ; (Abs.Q _) abs → ⊥-elim (∈KV-empty-⊥ abs)})
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈KV-empty-⊥ abs) })
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈KV-empty-⊥ abs) })
              (λ { _ _ _ _ (WithRSS.step _ _ {abs}) _ _ 
                 → ⊥-elim (∈KV-empty-⊥ abs) })
-}

{-

  --------------------------------
  -- Semantically Valid Records --

  abstractRecord : Record → Maybe Abs.Record
  abstractRecord (B {α} b p1 p2) 
    with initialAgreedHash ec ≟Hash getPrev b
  ...| yes _ = just (Abs.B (Abs.mkBlock (hash (encode (content b))) α nothing (getRound b)))
  ...| no  _ = just (Abs.B (Abs.mkBlock (hash (encode (content b))) α (just (getPrev b)) (getRound b)))
  abstractRecord (Q b p1 p2) = {!!}
  abstractRecord _ = nothing

  -- A record extends some other in a state if there exists
  -- a record chain in said state that ends on the record supposed
  -- to be extended
  data Extends (rss : RecordStoreState) : Abs.Record → Set where
     -- VCM: We might carry more information on this constructor
     extends : ∀{r r'}
             → (rInPool : r ∈BT rss)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties.
             -- → (r'New : lookup (rssPool rss) (hashR r') ≡ nothing)
             → (r'New : ¬ (r' ∈BT rss))
             → r ← r'
             → Extends rss r'
{-
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
-}

{-
  open import LibraBFT.Abstract.Records                                  ec 
  open import LibraBFT.Abstract.BFT                                      ec 
  open import LibraBFT.Abstract.Records.Extends             hash hash-cr ec 
  open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
  open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec

  hashRecord : Record → Hash
  hashRecord = hash ∘ encodeR

{-
  ∈BT-correct : (rss : RecordStoreState)(r : Record)
               → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ just r
  ∈BT-correct rss (B x) prf = lookup-correct (B x) (rssPool rss) prf
  ∈BT-correct rss (Q x) prf = lookup-correct (Q x) (rssPool rss) prf

  ∈BT-correct-⊥ : (rss : RecordStoreState)(r : Record)
                 → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ nothing → ⊥
  ∈BT-correct-⊥ = {!!}
-}

  ---------------------------------------
  -- Honesty and Dishonesty of Authors --

  data Dishonest (α : Author ec) : Set where
    same-order-diff-qcs 
      : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
      → q ≢ q'
      → voteOrder (∈QC-Vote q vα) ≡ voteOrder (∈QC-Vote q' vα')
      → Dishonest α

  DishonestM : Maybe (Author ec) → Set
  DishonestM nothing  = ⊥
  DishonestM (just α) = Dishonest α

  postulate
    ACCOUNTABILITY-OPP : ∀{α} → Honest α → Dishonest α → ⊥

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
    → (∀ {r} → r ∈BT rss → r ∈BT rss')
    → WithBT.RecordChain rss s → WithBT.RecordChain rss' s
  RecordChain-grow f WithBT.empty           
    = WithBT.empty
  RecordChain-grow f (WithBT.step rc x {p}) 
    = WithBT.step (RecordChain-grow f rc) x {f p}

  -- Inserting does not loose any records.
  insert-stable : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
                → {r : Record}
                → r ∈BT rss
                → r ∈BT (insert rss r' ext)
  insert-stable ext {I x} hyp = unit
  insert-stable (extends _ nc _) {B x} hyp = hs-insert-stable nc hyp
  insert-stable (extends _ nc _) {Q x} hyp = hs-insert-stable nc hyp

  -- If a record is not in store before insertion, but it is after
  -- the insertion, this record must have been the inserted one.
  insert-target : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
                → {r : Record}
                → ¬ (r ∈BT rss)
                → r ∈BT (insert rss r' ext)
                → r ≡ r'
  insert-target ext {I x} neg hyp = ⊥-elim (neg hyp)
  insert-target (extends _ nc _) {B x} neg hyp = hs-insert-target nc neg hyp
  insert-target (extends _ nc _) {Q x} neg hyp = hs-insert-target nc neg hyp

  -- Inserting a record is provably correct.
  insert-∈BT : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
              → r' ∈BT insert rss r' ext
  insert-∈BT {rss}{I _}(extends _ nc _) = unit
  insert-∈BT {rss}{B x}(extends _ nc _) = hs-insert-∈HS (B x) (rssPool rss) nc
  insert-∈BT {rss}{Q x}(extends _ nc _) = hs-insert-∈HS (Q x) (rssPool rss) nc

  insert-ok-correct : (rss : RecordStoreState)(r' : Record)(ext : Extends rss r')
            → ValidBT rss
            → Correct (insert rss r' ext)
  insert-ok-correct rss r' ext vrss s s∈post 
    with s ∈BT? rss
  ...| yes s∈rss = RecordChain-grow (insert-stable ext) (ValidBT.correct vrss s s∈rss)
  ...| no  s∉rss 
    rewrite insert-target ext s∉rss s∈post 
    with ext
  ...| extends {r = r} a b r←r' 
     = WithBT.step (RecordChain-grow (insert-stable {rss} (extends a b r←r')) 
                                      (ValidBT.correct vrss r a))
                    r←r' {insert-∈BT (extends a b r←r')}

  ---------------------
  -- VOTES ONCE RULE --

  -- If we have two proofs that α voted in QC q; these proofs
  -- are the same. Here is where we will need the IsSorted inside
  -- the qc! :)
  ∈QC-Vote-prop 
    : {α : Author ec}(q : QC) → (vα vα' : α ∈QC q) → vα ≡ vα'
  ∈QC-Vote-prop = {!!}

  insert-ok-votes-only-once : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidBT rss
            → VotesOnlyOnce (insert rss r ext)
  insert-ok-votes-only-once rss r ext vrss α hα {q} {q'} q∈rss q'∈rss vα vα' ord 
  -- 0. Are the QCs equal?
    with q ≟QC q'
  ...| yes refl rewrite ∈QC-Vote-prop q vα vα' = refl
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈BT? rss | (Q q') ∈BT? rss
  -- 1.1 Yes, they are old. Easy! Rely on the hypothesis that the previous
  --     state was correct.
  ...| yes qOld | yes q'Old 
     = ValidBT.votes-once-rule vrss α hα qOld q'Old vα vα' ord
  -- 1.2 No! One is old but the other is newly inserted. This must be impossible.
  ...| no  qNew | yes q'Old 
     -- But wait. If q has been inserted but not q'; but at
     -- the same time we have a proof that q extends the state, 
     -- the rounds of the QC's must be different, which render
     -- the QC's different altogether. Hence, α is Dishonest and
     -- we have proof!
     = ⊥-elim (ACCOUNTABILITY-OPP hα (same-order-diff-qcs {α} {q} {q'} vα vα' q≢q' ord)) 
  ...| yes qOld | no  q'New 
     = ⊥-elim (ACCOUNTABILITY-OPP hα (same-order-diff-qcs {α} {q} {q'} vα vα' q≢q' ord))
  -- 1.3 Both QCs are new; hence must have been inserted
  --     now. This means that they must be equal; Yet, we have
  --     just compared them before and found out they are not equal.
  ...| no  qNew | no  q'New 
    with trans (insert-target ext {Q q'} q'New q'∈rss) 
          (sym (insert-target ext {Q q} qNew q∈rss))
  ...| q≡q' = ⊥-elim (q≢q' (sym (Q-injective q≡q')))

  insert-ok-increasing-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidBT rss
            → IncreasingRound (insert rss r ext)
  insert-ok-increasing-round rss r ext vrss α hα {q} {q'} q∈rss q'∈rss va va' ord 
  -- 0. Are the QCs equal? Well, no, the orders are different
    with q ≟QC q'
  ...| yes refl = {!!} -- impossible!
  ...| no  q≢q' 
  -- 1. Are these old QCs or did we just insert them?
    with (Q q) ∈BT? rss | (Q q') ∈BT? rss
  -- 1.1. Both are old; simple. Use hypothesis
  ...| yes qOld | yes q'Old 
     = ValidBT.incr-round-rule vrss α hα qOld q'Old va va' ord
  -- 1.2. Both are new, impossible; we just saw they must be different.
  ...| no  qNew | no  q'New 
     = ⊥-elim (q≢q' (sym (Q-injective 
          (trans (insert-target ext {Q q'} q'New q'∈rss) 
          (sym (insert-target ext {Q q} qNew q∈rss))))))
  ...| yes qOld | no  q'New = {!!}
  ...| no  qNew | yes q'Old = {!!}


  insert-ok-locked-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidBT rss
            → LockedRound (insert rss r ext)
  insert-ok-locked-round rss r ext vrss = {!!}

  insert-ok : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidBT rss
            → ValidBT (insert rss r ext)
  insert-ok rss r ext vrss =
    valid-rss
      (insert-ok-correct          rss r ext vrss)
      (insert-ok-increasing-round rss r ext vrss)
      (insert-ok-votes-only-once  rss r ext vrss)
      (insert-ok-locked-round     rss r ext vrss)
-}
-}
