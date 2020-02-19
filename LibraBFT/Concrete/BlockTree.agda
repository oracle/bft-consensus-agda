{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

module LibraBFT.Concrete.BlockTree
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 
    (ec  : EpochConfig)
 where

  open import LibraBFT.Concrete.Util.KVMap
  open import LibraBFT.Concrete.Records

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

  α-Block : LinkableBlock → Abs.Block
  α-Block b' with (ebBlock ⇣) ((lbExecutedBlock ⇣) b')
  ...| b with (bdBlockType ⇣) ((bBlockData ⇣) b)
  ...| NilBlock = record
       { bId     = (bId ⇣) b
       ; bPrevQC = just (b ^∙ (bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙  vdParent ∙ biId))
       ; bRound  = b ^∙ bBlockData ∙ bdRound
       }
  ...| Genesis = record
       { bId     = b ^∙ bId
       ; bPrevQC = nothing
       ; bRound  = b ^∙ bBlockData ∙ bdRound
       }
  ...| Proposal cmd α = record
       { bId     = b ^∙ bId
       ; bPrevQC = just (b ^∙ bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙ vdParent ∙ biId)
       ; bRound  = b ^∙ bBlockData ∙ bdRound
       }

  α-Vote : (qc : QuorumCert)(valid : IsValidQC ec qc)
         → ∀ {as}
         → as ∈ qcVotes qc
         → Abs.Vote
  α-Vote qc v {author , sig , ord} as∈QC = record
    { vAuthor   = (ivaIdx (All-lookup (IsValidQC.ivqcValidAuthors v) as∈QC))
    ; vBlockUID = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; vRound    = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
    ; vOrder    = unsafeReadMeta ord -- VCM: here's the cliff hanger! if we just
                                     --      ord in here Agda will reject.
    }

  α-QC : Σ QuorumCert (IsValidQC ec) → Abs.QC
  α-QC (qc , valid) = record
    { qCertBlockId = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; qRound       = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
    ; qVotes       = All-reduce (α-Vote qc valid) (All-tabulate (λ x → x))
    ; qVotes-C1    = {!!} -- this proofs will come from the KV-store module
    ; qVotes-C2    = subst (_ ≤_) {!!} (IsValidQC.ivqcSizeOk valid)
    ; qVotes-C3    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self
    ; qVotes-C4    = All-reduce⁺ (α-Vote qc valid) (λ _ → refl) All-self 
    }

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
    = α-Block <M$> (lookup (Abs.bId b) ((btIdToBlock ⇣) bt)) ≡ just b
  (Abs.Q q) ∈BT bt 
    -- A qc is said to be in the abstract state iff there exists
    -- a qc that certifies the same block (i.e., with the same id).
    -- We don't particularly care for the list of votes or who authored it
    = (qcCertifies ⇣ ∘ proj₁) <M$> (lookup (Abs.qCertBlockId q) (BlockTree.btIdToQuorumCert bt))
      ≡ just (Abs.qCertBlockId q)

  _∈BT?_ : (r : Abs.Record)(bt : BlockTree) → Dec (r ∈BT bt)
  Abs.I     ∈BT? bt = yes unit
  (Abs.B b) ∈BT? bt 
    with lookup (Abs.bId b) (bt ^∙ btIdToBlock)
  ...| nothing = no (λ x → maybe-⊥ refl (sym x))
  ...| just r  
    with α-Block r Abs.≟Block b
  ...| yes refl = yes refl
  ...| no  ok   = no (ok ∘ just-injective)
  (Abs.Q q) ∈BT? bt
    with lookup (Abs.qCertBlockId q) (BlockTree.btIdToQuorumCert bt)
  ...| nothing = no λ x → maybe-⊥ refl (sym x)
  ...| just (qq , _) with (BlockInfo.biId (VoteData.vdProposed (QuorumCert.qcVoteData qq))) ≟UID Abs.qCertBlockId q
  ...| yes refl = yes refl
  ...| no xx    = no  (xx ∘ just-injective)

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

  -- TODO: fill out other fields
  emptyBT : BlockTree
  emptyBT = record
    { btIdToBlock      = empty
    ; btIdToQuorumCert = empty
    ; btEpochConfig    = meta ec
    }

  empty-Correct : Correct emptyBT
  empty-Correct Abs.I     _    = WithRSS.empty
  empty-Correct (Abs.B b) imp
    = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ (α-Block <M$>_))
                                 (sym (kvm-empty {k = Abs.bId b}))
                                 refl))
  empty-Correct (Abs.Q q) imp
    = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ (((qcCertifies ⇣) ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))

  empty-IncreasingRound : IncreasingRound emptyBT
  empty-IncreasingRound α x {q = q} x₁ x₂ va va' x₃
    = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ (((qcCertifies ⇣) ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))

  empty-VotesOnlyOnce : VotesOnlyOnce emptyBT
  empty-VotesOnlyOnce α x {q = q} x₁ x₂ va va' x₃
    = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ (((qcCertifies ⇣) ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))


  empty-LockedRound : LockedRound emptyBT
  empty-LockedRound _ _ _ _ (WithRSS.step {r' = Abs.Q q'} _ _ {abs}) _ _
    = ⊥-elim (maybe-⊥ abs (subst ((_≡ nothing) ∘ (((qcCertifies ⇣) ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q'}))
                                 refl))

  -- And now this is really trivial
  emptyBT-valid : ValidBT emptyBT
  emptyBT-valid =
    valid-bt empty-Correct
             empty-IncreasingRound
             empty-VotesOnlyOnce
             empty-LockedRound

  --------------------------------
  -- Semantically Valid Records --

  data canInsert {ec : EpochConfig} (bt : BlockTree) (ec≡ : unsafeReadMeta (BlockTree.btEpochConfig bt) ≡ ec) : (r' : Abs.Record) → Set where
    B : {ab : Abs.Block}
      → {cb : LinkableBlock}
      → ab ≡ α-Block cb
      → lookup (Abs.bId ab) ((btIdToBlock ⇣) bt) ≡ nothing
      → canInsert bt ec≡ (Abs.B ab)
    Q : {aq : Abs.QC}
      → {cq : Σ QuorumCert (IsValidQC ((unsafeReadMeta ∘ BlockTree.btEpochConfig) bt))}
      → Abs.qCertBlockId aq ≡ (qcCertifies ⇣) (proj₁ cq)
      → lookup (Abs.qCertBlockId aq) (BlockTree.btIdToQuorumCert bt) ≡ nothing
      → canInsert bt ec≡ (Abs.Q aq)

  -- A record extends some other in a state if there exists
  -- a record chain in said state that ends on the record supposed
  -- to be extended
  data Extends (bt : BlockTree) : Abs.Record → Set where
     -- VCM: We might carry more information on this constructor
     extends : ∀{r r'}
             → (ec≡ : unsafeReadMeta (BlockTree.btEpochConfig bt) ≡ ec)
             → (rInPool : r ∈BT bt)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties.
             → (r'New : canInsert bt ec≡ r')
             → r ← r'
             → Extends bt r'


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
-}


{-
  hashRecord : Abs.Record → Hash
  hashRecord = hash ∘ encodeR

  ∈BT-correct : (rss : RecordStoreState)(r : Record)
               → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ just r
  ∈BT-correct rss (B x) prf = lookup-correct (B x) (rssPool rss) prf
  ∈BT-correct rss (Q x) prf = lookup-correct (Q x) (rssPool rss) prf

  ∈BT-correct-⊥ : (rss : RecordStoreState)(r : Record)
                 → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ nothing → ⊥
  ∈BT-correct-⊥ = {!!}
-}
{-
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
-}

  --------------------------
  -- Insertion of Records --

  insert-block : ∀ (bt : BlockTree)(ab : Abs.Block)
               → (ext : Extends bt (Abs.B ab))
               → BlockTree
  insert-block bt ab (extends ec≡ rInPool (B {_} {b} abdGood idAvail) x) =
                 record bt {btIdToBlock = kvm-insert
                                            (Abs.bId ab)
                                            b
                                            ((btIdToBlock ⇣) bt)
                                            idAvail}

  insert-qc : ∀ (bt : BlockTree)(aq : Abs.QC)
               → (ext : Extends bt (Abs.Q aq))
               → BlockTree
  insert-qc bt aq (extends ec≡ rInPool (Q {_} {cqm} _ idAvail) x) =
                 record bt {btIdToQuorumCert = kvm-insert
                                                (Abs.qCertBlockId aq)
                                                cqm
                                                (BlockTree.btIdToQuorumCert bt)
                                            idAvail}

  insert-init  : ∀ (bt : BlockTree)(ext : Extends bt Abs.I)
               → BlockTree
  insert-init  bt (extends _ _ () _)


  insert : ∀ (bt : BlockTree)(r' : Abs.Record)(ext : Extends bt r')
         → BlockTree
  insert bt  Abs.I    ext = insert-init bt ext
  insert bt (Abs.B b) ext = insert-block bt b ext
  insert bt (Abs.Q q) ext = insert-qc bt q ext

  ---------------------
  -- IS CORRECT RULE --

  -- We can always inject a record chain from a recordstorestate
  -- into another by proving the later contains at least all the
  -- records of the former.
  RecordChain-grow
    : {bt bt' : BlockTree}{s : Abs.Record}
    → (∀ {r} → r ∈BT bt → r ∈BT bt')
    → WithRSS.RecordChain bt s → WithRSS.RecordChain bt' s
  RecordChain-grow f WithRSS.empty
    = WithRSS.empty
  RecordChain-grow f (WithRSS.step rc x {p})
    = WithRSS.step (RecordChain-grow f rc) x {f p}

  -- Inserting does not lose any records.
  insert-stable : {bt : BlockTree}{r' : Abs.Record}(ext : Extends bt r')
                → {r : Abs.Record}
                → r ∈BT bt
                → r ∈BT (insert bt r' ext)
  insert-stable ext {Abs.I} b = unit

  -- TODO: eliminate warnings -- unsolved meta.  Key is that Blocks don't extend Blocks
  --       and QCs don't extend QCs.
  insert-stable {bt} (extends _ _ (B _ _) _) {Abs.Q ()}
  insert-stable {bt} (extends _ _ (Q _ _) _) {Abs.B ()}

  -- MSM: can't help feeling I overcomplicated these proofs
  insert-stable {bt} (extends _ _ (B _ idAvail) _) {Abs.B ab} hyp
    with         (lookup (Abs.bId ab)) ((btIdToBlock ⇣) bt) |
         inspect (lookup (Abs.bId ab)) ((btIdToBlock ⇣) bt)
  ...| nothing | _ = ⊥-elim (maybe-⊥ hyp refl)
  ...| just lb | [ xx ] =
         subst ((_≡ just ab) ∘ (α-Block <M$>_))
               (sym (lookup-stable-1 idAvail xx))
               (trans (cong (α-Block <M$>_) xx) hyp)

  insert-stable {bt} (extends _ _ (Q _ idAvail) _) {Abs.Q aq} hyp
    with         (lookup (Abs.qCertBlockId aq)) (BlockTree.btIdToQuorumCert bt) |
         inspect (lookup (Abs.qCertBlockId aq)) (BlockTree.btIdToQuorumCert bt)
  ...| nothing | _ = ⊥-elim (maybe-⊥ hyp refl)
  ...| just qcp | [ xx ] =
         subst ((_≡ just (Abs.qCertBlockId aq)) ∘ (((qcCertifies ⇣) ∘ proj₁) <M$>_))
               (sym (lookup-stable-1 idAvail xx))
               (trans (cong ((((qcCertifies ⇣) ∘ proj₁) <M$>_)) xx) hyp)

--   -- If a record is not in store before insertion, but it is after
--   -- the insertion, this record must have been the inserted one.
--   insert-target : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
--                 → {r : Record}
--                 → ¬ (r ∈BT rss)
--                 → r ∈BT (insert rss r' ext)
--                 → r ≡ r'
--   insert-target ext {I x} neg hyp = ⊥-elim (neg hyp)
--   insert-target (extends _ nc _) {B x} neg hyp = hs-insert-target nc neg hyp
--   insert-target (extends _ nc _) {Q x} neg hyp = hs-insert-target nc neg hyp

--   -- Inserting a record is provably correct.
--   insert-∈BT : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
--               → r' ∈BT insert rss r' ext
--   insert-∈BT {rss}{I _}(extends _ nc _) = unit
--   insert-∈BT {rss}{B x}(extends _ nc _) = hs-insert-∈HS (B x) (rssPool rss) nc
--   insert-∈BT {rss}{Q x}(extends _ nc _) = hs-insert-∈HS (Q x) (rssPool rss) nc

--   insert-ok-correct : (rss : RecordStoreState)(r' : Record)(ext : Extends rss r')
--             → ValidBT rss
--             → Correct (insert rss r' ext)
--   insert-ok-correct rss r' ext vrss s s∈post 
--     with s ∈BT? rss
--   ...| yes s∈rss = RecordChain-grow (insert-stable ext) (ValidBT.correct vrss s s∈rss)
--   ...| no  s∉rss 
--     rewrite insert-target ext s∉rss s∈post 
--     with ext
--   ...| extends {r = r} a b r←r' 
--      = WithBT.step (RecordChain-grow (insert-stable {rss} (extends a b r←r')) 
--                                       (ValidBT.correct vrss r a))
--                     r←r' {insert-∈BT (extends a b r←r')}

--   ---------------------
--   -- VOTES ONCE RULE --

--   -- If we have two proofs that α voted in QC q; these proofs
--   -- are the same. Here is where we will need the IsSorted inside
--   -- the qc! :)
--   ∈QC-Vote-prop 
--     : {α : Author ec}(q : QC) → (vα vα' : α ∈QC q) → vα ≡ vα'
--   ∈QC-Vote-prop = {!!}

--   insert-ok-votes-only-once : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
--             → ValidBT rss
--             → VotesOnlyOnce (insert rss r ext)
--   insert-ok-votes-only-once rss r ext vrss α hα {q} {q'} q∈rss q'∈rss vα vα' ord 
--   -- 0. Are the QCs equal?
--     with q ≟QC q'
--   ...| yes refl rewrite ∈QC-Vote-prop q vα vα' = refl
--   ...| no  q≢q' 
--   -- 1. Are these old QCs or did we just insert them?
--     with (Q q) ∈BT? rss | (Q q') ∈BT? rss
--   -- 1.1 Yes, they are old. Easy! Rely on the hypothesis that the previous
--   --     state was correct.
--   ...| yes qOld | yes q'Old 
--      = ValidBT.votes-once-rule vrss α hα qOld q'Old vα vα' ord
--   -- 1.2 No! One is old but the other is newly inserted. This must be impossible.
--   ...| no  qNew | yes q'Old 
--      -- But wait. If q has been inserted but not q'; but at
--      -- the same time we have a proof that q extends the state, 
--      -- the rounds of the QC's must be different, which render
--      -- the QC's different altogether. Hence, α is Dishonest and
--      -- we have proof!
--      = ⊥-elim (ACCOUNTABILITY-OPP hα (same-order-diff-qcs {α} {q} {q'} vα vα' q≢q' ord)) 
--   ...| yes qOld | no  q'New 
--      = ⊥-elim (ACCOUNTABILITY-OPP hα (same-order-diff-qcs {α} {q} {q'} vα vα' q≢q' ord))
--   -- 1.3 Both QCs are new; hence must have been inserted
--   --     now. This means that they must be equal; Yet, we have
--   --     just compared them before and found out they are not equal.
--   ...| no  qNew | no  q'New 
--     with trans (insert-target ext {Q q'} q'New q'∈rss) 
--           (sym (insert-target ext {Q q} qNew q∈rss))
--   ...| q≡q' = ⊥-elim (q≢q' (sym (Q-injective q≡q')))

--   insert-ok-increasing-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
--             → ValidBT rss
--             → IncreasingRound (insert rss r ext)
--   insert-ok-increasing-round rss r ext vrss α hα {q} {q'} q∈rss q'∈rss va va' ord 
--   -- 0. Are the QCs equal? Well, no, the orders are different
--     with q ≟QC q'
--   ...| yes refl = {!!} -- impossible!
--   ...| no  q≢q' 
--   -- 1. Are these old QCs or did we just insert them?
--     with (Q q) ∈BT? rss | (Q q') ∈BT? rss
--   -- 1.1. Both are old; simple. Use hypothesis
--   ...| yes qOld | yes q'Old 
--      = ValidBT.incr-round-rule vrss α hα qOld q'Old va va' ord
--   -- 1.2. Both are new, impossible; we just saw they must be different.
--   ...| no  qNew | no  q'New 
--      = ⊥-elim (q≢q' (sym (Q-injective 
--           (trans (insert-target ext {Q q'} q'New q'∈rss) 
--           (sym (insert-target ext {Q q} qNew q∈rss))))))
--   ...| yes qOld | no  q'New = {!!}
--   ...| no  qNew | yes q'Old = {!!}


--   insert-ok-locked-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
--             → ValidBT rss
--             → LockedRound (insert rss r ext)
--   insert-ok-locked-round rss r ext vrss = {!!}

--   insert-ok : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
--             → ValidBT rss
--             → ValidBT (insert rss r ext)
--   insert-ok rss r ext vrss =
--     valid-rss
--       (insert-ok-correct          rss r ext vrss)
--       (insert-ok-increasing-round rss r ext vrss)
--       (insert-ok-votes-only-once  rss r ext vrss)
--       (insert-ok-locked-round     rss r ext vrss)
-- -}
