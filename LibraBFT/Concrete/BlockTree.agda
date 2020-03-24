-- {-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

module LibraBFT.Concrete.BlockTree
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec  : Meta EpochConfig)
 where

  open import LibraBFT.Concrete.Util.KVMap
  open import LibraBFT.Concrete.Records


  open import LibraBFT.Concrete.Consensus.Types.EpochIndep
  open import LibraBFT.Concrete.Consensus.Types.EpochDep ec

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
  α-Block b' with _ebBlock (_lbExecutedBlock b')
  ...| b with _bdBlockType (_bBlockData b)
  ...| NilBlock = record
       { bId     = _bId b
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

  α-Vote : (qc : QuorumCert)(valid : IsValidQC qc)
         → ∀ {as}
         → as ∈ qcVotes qc
         → Abs.Vote
  α-Vote qc v {author , sig , ord} as∈QC = record
    { vAuthor   = {!!} -- (_ivaIdx (All-lookup (IsValidQC._ivqcValidAuthors v) as∈QC))  -- TODO: this is broken as _ivqcValidAuthors has gone way, need to fix
    ; vBlockUID = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; vRound    = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
    ; vOrder    = unsafeReadMeta ord -- VCM: here's the cliff hanger! if we just
                                     --      ord in here Agda will reject.
    }

  α-QC : Σ QuorumCert IsValidQC → Abs.QC
  α-QC (qc , valid) = record
    { qCertBlockId = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; qRound       = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
    ; qVotes       = All-reduce (α-Vote qc valid) (All-tabulate (λ x → x))
    ; qVotes-C1    = {!!} -- this proofs will come from the KV-store module
    ; qVotes-C2    = subst (_ ≤_) {!!} (IsValidQC._ivqcSizeOk valid)
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

  -- The abstract model considers two QC's to be equal iff they
  -- certify the same block; yet, this is a little too weak for us.
  -- From the concrete point of view, an Abs.QC, αq, is said to be in the
  -- blocktree iff ∃ γq such that lookup (qCertBlock αq) ≡ just γq and
  -- γq ≋QC αq, defined next. 
  --
  -- TODO: find better symbol?
  _≋QC_ : Abs.QC → Abs.QC → Set
  γq ≋QC αq = γq Abs.≈QC αq × Abs.qRound γq ≡ Abs.qRound αq


  -- VCM: We really need to invoke the abstraction function here; otherwise
  -- we have no guarantee that the rest of the fields of the abstract block
  -- are correct. This is what ensures the abstract model will not conjure blocks
  -- out of nowhere.
  _∈BT_ : Abs.Record → BlockTree → Set
  Abs.I     ∈BT bt = Unit -- The initial record is not really *in* the record store,
  (Abs.B b) ∈BT bt 
    = α-Block <M$> (lookup (Abs.bId b) (_btIdToBlock bt)) ≡ just b
  (Abs.Q q) ∈BT bt 
    -- A qc is said to be in the abstract state iff there exists
    -- a qc that certifies the same block (i.e., with the same id).
    -- We don't particularly care for the list of votes or who authored it
    = maybe ((q ≋QC_) ∘ α-QC) ⊥ (lookup (Abs.qCertBlockId q) (_btIdToQuorumCert bt))

  _∈BT?_ : (r : Abs.Record)(bt : BlockTree) → Dec (r ∈BT bt)
  Abs.I     ∈BT? bt = yes unit
  (Abs.B b) ∈BT? bt 
    with lookup (Abs.bId b) (_btIdToBlock bt)
  ...| nothing = no (λ x → maybe-⊥ refl (sym x))
  ...| just r  
    with α-Block r Abs.≟Block b
  ...| yes refl = yes refl
  ...| no  ok   = no (ok ∘ just-injective)
  (Abs.Q q) ∈BT? bt
    with lookup (Abs.qCertBlockId q) (BlockTree._btIdToQuorumCert bt)
  ...| nothing = no id
  ...| just (qq , _) 
    with _qcCertifies qq ≟UID Abs.qCertBlockId q
  ...| no xx    = no (λ x → xx (sym (proj₁ x)))
  ...| yes refl  
    with _qcRound qq ≟ℕ Abs.qRound q
  ...| no xx    = no (λ x → xx (sym (proj₂ x)))
  ...| yes refl = yes (refl , refl)

  ∈BT-irrelevant : ∀{r bt}(p₀ p₁ : r ∈BT bt) → p₀ ≡ p₁
  ∈BT-irrelevant {Abs.I} unit unit    = refl
  ∈BT-irrelevant {Abs.B x} {st} p0 p1 = ≡-irrelevant p0 p1
  ∈BT-irrelevant {Abs.Q x} {st} p0 p1 
    with lookup (Abs.qCertBlockId x) (_btIdToQuorumCert st)
  ...| nothing = ⊥-elim p1
  ...| just γ  = cong₂ _,_ (≡-irrelevant (proj₁ p0) (proj₁ p1)) 
                           (≡-irrelevant (proj₂ p0) (proj₂ p1))

  instance
    abstractBT : isRecordStoreState BlockTree
    abstractBT = record
      { isInPool            = _∈BT_
      ; isInPool-irrelevant = λ {r} {bt} → ∈BT-irrelevant {r} {bt}
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
    { _btIdToBlock               = empty
    ; :btRootId                  = initialAgreedHash (unsafeReadMeta ec)  -- These unsafeReadMetas will go away when
    ; _btHighestCertifiedBlockId = initialAgreedHash (unsafeReadMeta ec)  -- we do real epoch changes as these hashes will
    ; _btHighestQuorumCert       = {!!} -- ??                             -- come from somewhere else.  Similarly for
    ; _btHighestCommitCert       = {!!} -- ??                             -- these initial QCs.
    ; _btPendingVotes            = mkPendingVotes empty empty
    ; _btPrunedBlockIds          = []
    ; _btMaxPrunedBlocksInMem    = 0 
    ; _btIdToQuorumCert          = empty
    }

  empty-Correct : Correct emptyBT
  empty-Correct Abs.I     _    = WithRSS.empty
  empty-Correct (Abs.B b) imp
    = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ (α-Block <M$>_))
                                 (sym (kvm-empty {k = Abs.bId b}))
                                 refl))
  empty-Correct (Abs.Q q) imp
    rewrite kvm-empty {Val = Σ QuorumCert IsValidQC} 
                      {k = Abs.qCertBlockId q} 
          = ⊥-elim imp 

  empty-IncreasingRound : IncreasingRound emptyBT
  empty-IncreasingRound α x {q = q} x₁ x₂ va va' x₃
    rewrite kvm-empty {Val = Σ QuorumCert IsValidQC} 
                      {k = Abs.qCertBlockId q} 
          = ⊥-elim x₁

  empty-VotesOnlyOnce : VotesOnlyOnce emptyBT
  empty-VotesOnlyOnce α x {q = q} x₁ x₂ va va' x₃
    rewrite kvm-empty {Val = Σ QuorumCert IsValidQC} 
                      {k = Abs.qCertBlockId q} 
          = ⊥-elim x₁

  empty-LockedRound : LockedRound emptyBT
  empty-LockedRound _ _ _ _ (WithRSS.step {r' = Abs.Q q'} _ _ {abs}) _ _
    = ⊥-elim (subst (λ P₁ → maybe ((q' ≋QC_) ∘ α-QC) ⊥ P₁) 
                    (kvm-empty {k = Abs.qCertBlockId q'}) abs)

  -- And now this is really trivial
  emptyBT-valid : ValidBT emptyBT
  emptyBT-valid =
    valid-bt empty-Correct
             empty-IncreasingRound
             empty-VotesOnlyOnce
             empty-LockedRound

  --------------------------------
  -- Semantically Valid Records --

  -- We can always inject a record chain from a recordstorestate
  -- into another by proving the later contains at least all the
  -- records of the former.
  rc-grow
    : {bt bt' : BlockTree}{s : Abs.Record}
    → (∀ {r} → r ∈BT bt → r ∈BT bt')
    → WithRSS.RecordChain bt s → WithRSS.RecordChain bt' s
  rc-grow f WithRSS.empty
    = WithRSS.empty
  rc-grow f (WithRSS.step {_} {r} rc x {p})
    = WithRSS.step (rc-grow (λ {r₀} → f {r₀}) rc) x {f {r} p}

  -- We can transport a record chain to a unrelated state
  -- as long as all of its records are in there.
  rc-transp
    : {bt bt' : BlockTree}{s : Abs.Record}
    → (rc : WithRSS.RecordChain bt s) 
    → (∀{r} → WithRSS._∈RC_ bt r rc → r ∈BT bt')
    → WithRSS.RecordChain bt' s
  rc-transp WithRSS.empty f 
    = WithRSS.empty
  rc-transp (WithRSS.step rc x {p}) f 
    = WithRSS.step (rc-transp rc (λ r∈rc → f (WithRSS.there x r∈rc))) 
                   x {f WithRSS.here}

  -- 'canInsert bt r' is just an inspectable synonym for '¬ (r ∈BT bt)'; actually,
  -- makes me thing why not using the later...
  data canInsert (bt : BlockTree) : (r' : Abs.Record) → Set where
    B : (cb : Abs.Block)
      → lookup (Abs.bId cb) (_btIdToBlock bt) ≡ nothing
      → canInsert bt (Abs.B cb)
    Q : (qc : Abs.QC)
      → lookup (Abs.qCertBlockId qc) (_btIdToQuorumCert bt) ≡ nothing
      → canInsert bt (Abs.Q qc)

  -- An abstract record |r'| is said to extend the block tree if there exists
  -- a record chain |rc| in the block tree suchthat |r'| can be appended to.
  data Extends (bt : BlockTree) : Abs.Record → Set where
     extends : ∀{r r'}
             → (rInPool : r ∈BT bt)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties; this will be enforced by the
             -- 'canInsert' type.
             → (r'New : canInsert bt r')
             → r ← r'
             → Extends bt r'

  ExtendsB : BlockTree → LinkableBlock → Set
  ExtendsB bt = Extends bt ∘ Abs.B ∘ α-Block

  ExtendsQC : BlockTree → Σ QuorumCert IsValidQC → Set
  ExtendsQC bt = Extends bt ∘ Abs.Q ∘ α-QC

  ---------------------------------------
  -- Properties About Valid BlockTrees --

  -- In a valid BlockTree; if a given QC certifies a block, then
  -- such block has a concrete counterpart that belongs in the block tree.
  qc-certifies-closed-conc : (bt : BlockTree) → Correct bt
                           → ∀{q} → (Abs.Q q) ∈BT bt
                           → ∃[ cb ] (lookup (Abs.qCertBlockId q) (_btIdToBlock bt) ≡ just cb)
  qc-certifies-closed-conc bt correct {q} q∈bt 
    with correct (Abs.Q q) q∈bt
  ...| WithRSS.step {Abs.B b} (WithRSS.step _ _ {b∈bt}) (B←Q refl refl) 
    with <M$>-univ α-Block (lookup (Abs.bId b) (_btIdToBlock bt)) b∈bt
  ...| (cb , inThere , _) = cb , inThere

  ---------------------------------
  -- Insertion of Blocks and QCs --
  --
  -- We will handle insertions of blocks and qcs separately,
  -- as these manipulate two different fields of our BlockTree.

  insert-block : (bt : BlockTree)(cb : LinkableBlock)(ext : ExtendsB bt cb)
               → BlockTree
  insert-block bt cb (extends rInPool canI x)
    with α-Block cb | canI
  ...| absCB | B .absCB prf 
     = record bt { _btIdToBlock = kvm-insert (Abs.bId absCB) cb 
                                         (_btIdToBlock bt) prf }

  insert-qc : (bt : BlockTree)(qc : Σ QuorumCert IsValidQC)(ext : ExtendsQC bt qc)
            → BlockTree
  insert-qc bt qc (extends rInPool canI x) 
    with α-QC qc | canI
  ...| absQC | Q .absQC prf 
     = record bt { _btIdToQuorumCert = kvm-insert (Abs.qCertBlockId absQC) qc
                                              (_btIdToQuorumCert bt) prf }

  -- ** Properties
  --
  -- *** Insertion of Blocks
 
  -- I'm parametrizing over bt and cb, but can't really put ExtendsB in here
  -- since we often need to pattern-match over it.
  module InsertBlockLemmas (bt : BlockTree)(cb : LinkableBlock) where
    open WithRSS

    -- Inserting does not lose any records; be it for blocks or QCs
    stable : (ext : ExtendsB bt cb){r : Abs.Record} 
           → r ∈BT bt → r ∈BT (insert-block bt cb ext)
    stable _                       {Abs.I}   r∈bt = unit
    stable (extends m (B _ prf) o) {Abs.Q x} r∈bt = r∈bt
    stable (extends m (B _ prf) o) {Abs.B x} r∈bt 
      with <M$>-univ α-Block (lookup (Abs.bId x) (_btIdToBlock bt)) r∈bt
    ...| (lkupRes , isJust , αres)
      rewrite lookup-stable {k' = Abs.bId x} {v' = cb} prf isJust 
            = cong just αres

    -- Inserting blocks does not interfere with _btIdToQuorumCert
    no-interf : (ext : ExtendsB bt cb)
              → _btIdToQuorumCert (insert-block bt cb ext)
              ≡ _btIdToQuorumCert bt
    no-interf (extends _ (B _ _) _) = refl

    -- If a record was not in bt, but is in (insert cb bt), said record must
    -- be the inserted one.
    target : (ext : ExtendsB bt cb)
           → {r : Abs.Record}
           → ¬ (r ∈BT bt)
           → r ∈BT (insert-block bt cb ext)
           → r ≡ Abs.B (α-Block cb)
    target ext {Abs.I}   neg hyp = ⊥-elim (neg hyp)
    target ext {Abs.Q x} neg hyp 
      rewrite no-interf ext = ⊥-elim (neg hyp) 
    target ext@(extends m (B _ prf) o) {Abs.B x} neg hyp 
      with <M$>-univ α-Block (lookup (Abs.bId x) (_btIdToBlock (insert-block bt cb ext))) hyp 
    ...| (lkupRes , isJust , refl) 
      with insert-target prf (λ { x → neg (cong (α-Block <M$>_) x) }) isJust
    ...| _ , refl  = refl

    -- The inserted record is an element of the update blocktree.
    elem : (ext : ExtendsB bt cb) → Abs.B (α-Block cb) ∈BT insert-block bt cb ext
    elem (extends rInPool (B res notThere) x) 
      rewrite lookup-correct {k = Abs.bId (α-Block cb)} 
                             {v = cb} 
                             {kvm = bt ^∙ btIdToBlock} 
                             notThere 
            = refl

    -- Inserting in a correct blocktree yeilds a correct blocktree.
    correct : (ext : ExtendsB bt cb) → Correct bt → Correct (insert-block bt cb ext)
    correct ext cbt s s∈post 
      with s ∈BT? bt 
    ...| yes s∈bt = rc-grow (λ {r} r∈bt → stable ext {r} r∈bt) (cbt s s∈bt)
    ...| no  s∉bt 
      rewrite target ext {s} s∉bt s∈post 
      with ext
    ...| extends {r = r} a canI r←r' 
       = step (rc-grow (λ {r₀} r₀∈bt → stable (extends a canI r←r') {r₀} r₀∈bt) (cbt r a)) 
              r←r' {elem (extends a canI r←r')}

    -- The proof for increasing round rule is easy; insert-block does
    -- not interfere with quorum certificates.
    incr-round : (ext : ExtendsB bt cb) → ValidBT bt → IncreasingRound (insert-block bt cb ext)
    incr-round ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp
      -- Both QC's must be old; since we just inserted a block. 
      rewrite no-interf ext
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    ...| no imp   | _         = ⊥-elim (imp q∈bt)
    ...| yes qOld | no  imp   = ⊥-elim (imp q'∈bt)
    ...| yes qOld | yes q'Old = ValidBT.incr-round-rule valid α hα {q} {q'} qOld q'Old va va' hyp

    -- Same for votes-only-once; there is no interference with quorum certificates
    votes-once : (ext : ExtendsB bt cb) → ValidBT bt → VotesOnlyOnce (insert-block bt cb ext)
    votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp
      -- Both QC's must be old; since we just inserted a block. 
      rewrite no-interf ext
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    ...| no imp   | _         = ⊥-elim (imp q∈bt)
    ...| yes qOld | no  imp   = ⊥-elim (imp q'∈bt)
    ...| yes qOld | yes q'Old = ValidBT.votes-once-rule valid α hα {q} {q'} qOld q'Old va va' hyp


    -- ** The Odyssey of the LockedRound **

    pres-Q∈BT : (ext : ExtendsB bt cb) 
              → ∀{q} → Abs.Q q ∈BT (insert-block bt cb ext) → Abs.Q q ∈BT bt
    pres-Q∈BT ext hyp rewrite no-interf ext = hyp

    pres-B∈BT : (ext : ExtendsB bt cb)
              → ∀{b} → Abs.B b ∈BT insert-block bt cb ext
              → Abs.bId b ≢ Abs.bId (α-Block cb)
              → Abs.B b ∈BT bt
    pres-B∈BT ext@(extends _ (B _ x) _) {b} hyp nothd
      with <M$>-univ α-Block (lookup (Abs.bId b) (_btIdToBlock (insert-block bt cb ext))) hyp
    ...| (bb , isJust , refl) 
      rewrite lookup-stable-2 x isJust nothd = refl

    -- A freshly inserted block is uncertifiable; in other words, for any
    -- quorum certificaet that belongs in (insert-block bt cb ext), said QC 
    -- cant certify cb.
    uncertifiable : (ext : ExtendsB bt cb)
                  → Correct bt
                  → ∀{q} → Abs.Q q ∈BT insert-block bt cb ext
                  → Abs.qCertBlockId q ≢ Abs.bId (α-Block cb)
    uncertifiable ext correct {q} q∈bt' refl
      with qc-certifies-closed-conc bt correct {q} (pres-Q∈BT ext {q} q∈bt')
    ...| (_ , cb∈bt) 
      with ext
    ...| extends _ (B _ cbNew) _ = maybe-⊥ cb∈bt cbNew

    mutual
     is-not-cb : (ext : ExtendsB bt cb) → Correct bt
               → ∀{b}(rc : RecordChain (insert-block bt cb ext) (Abs.B b))
               → Abs.bId b ≢ Abs.bId (α-Block cb)
               → ∀{r} → _∈RC_ (insert-block bt cb ext) r rc
               → r ∈BT bt
     is-not-cb ext cor rc hyp (transp {_} {rc₀} old eq) 
       = is-not-cb ext cor rc₀ hyp old
     is-not-cb ext@(extends _ (B αbt btNew) _) cor {b} (step rc _ {prf}) hyp (here) 
       with <M$>-univ α-Block (lookup (Abs.bId b) (_btIdToBlock (insert-block bt cb ext))) prf
     ...| (lb , isthere , refl) 
       rewrite lookup-stable-2 btNew isthere hyp 
             = refl
     is-not-cb ext cor (I←B i0 i1 [ b∈bt ]↝ empty) hyp (there p x {prf}) 
       rewrite ∈RC-empty-I (insert-block bt cb ext) x = unit
     is-not-cb ext cor (Q←B q0 q1 [ b∈bt ]↝ rc)    hyp (there p x {prf}) 
       = doesnt-use-cb ext cor rc x

     doesnt-use-cb : (ext : ExtendsB bt cb) → Correct bt
                   → ∀{q}(rc : RecordChain (insert-block bt cb ext) (Abs.Q q))
                   → ∀{r} → _∈RC_ (insert-block bt cb ext) r rc
                   → r ∈BT bt
     doesnt-use-cb ext cor rc (transp {_} {rc₀} old eq) 
       = doesnt-use-cb ext cor rc₀ old
     doesnt-use-cb ext cor (step _ _ {q∈bt'}) {r} (here) 
       rewrite no-interf ext = q∈bt'
     doesnt-use-cb ext cor {q} (B←Q b0 b1 [ q∈bt' ]↝ rc) {r} (there p x {prf})
       = is-not-cb ext cor rc (λ h → uncertifiable ext cor {q} prf (trans (sym b1) h)) x

    -- If we have a record chain leading to a quorum certificate in the 
    -- state that results from the insertion of a block; we can have the same record chain
    -- wihtout said block.
    rc-shrink : (ext : ExtendsB bt cb) 
              → Correct bt → ∀{q}
              → RecordChain (insert-block bt cb ext) (Abs.Q q)
              → RecordChain bt (Abs.Q q)
    rc-shrink ext cor rc = rc-transp rc (doesnt-use-cb ext cor rc)

    -- Here we must prove that transporting a record chain doesn't change
    -- its last round. In fact, I would love to have something like:
    --
    -- > rc ≅ rc-transp rc f
    --
    -- But we can't prove that (the base cases of each side have different types
    -- and hence refl can't be used). 
    --
    -- This means we need one lemma for each 'accessor' of record chains
    -- we need. Right now we just need prevRound; lets pray it stays this way
    -- and we should be fine.
    rc-shrink-prevRound
      : (ext : ExtendsB bt cb)(cor : Correct bt)
      → ∀{q}(rc : RecordChain (insert-block bt cb ext) (Abs.Q q)) 
      → prevRound rc ≡ prevRound (rc-shrink ext cor rc)
    rc-shrink-prevRound ext cor (step (step rc (I←B _ _)) (B←Q _ refl))         = refl
    rc-shrink-prevRound ext cor (step (step (step _ _) (Q←B _ _)) (B←Q _ refl)) = refl

    -- Here, for instance, we need to go over the elements of the k-chain
    -- simply to let Agda reduce rc-shrink (patter matching on the k-chain
    -- yeilds info about the shabe of the recordchain, which in turn, reduces rc-shrink)
    kc-shrink : ∀{R n}(ext : ExtendsB bt cb)
              → (corr : Correct bt)
              → ∀{q}{rc : RecordChain (insert-block bt cb ext) (Abs.Q q)}
              → 𝕂-chain (insert-block bt cb ext) R n rc 
              → 𝕂-chain bt R n (rc-shrink ext corr rc)
    kc-shrink ext cor 0-chain = 0-chain
    kc-shrink ext cor (s-chain (I←B i0 i1) prf b←q 0-chain) 
      = s-chain (I←B i0 i1) prf b←q 0-chain
    kc-shrink ext cor (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain) 
      = s-chain (Q←B q0 q1) prf (B←Q b0 refl) 0-chain
    kc-shrink ext cor (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) 
      = s-chain (Q←B q0 q1) prf (B←Q b0 refl) (kc-shrink ext cor {q'} c) 

    -- We should be able to "easily" prove that kc-shrink does /not/
    -- alter the blocks of the kchain.
    kc-shrink-≡b : ∀{R n}(ext : ExtendsB bt cb)
                 → (corr : Correct bt)
                 → ∀{q}{rc : RecordChain (insert-block bt cb ext) (Abs.Q q)}
                 → (i : Fin n)
                 → (kc : 𝕂-chain (insert-block bt cb ext) R n rc)
                 → kchainBlock bt i (kc-shrink ext corr kc) ≡ kchainBlock (insert-block bt cb ext) i kc
    kc-shrink-≡b ext corr () 0-chain
    -- Base case; easy byt requires to match on a lot of stuff to reduce kc-shrink
    kc-shrink-≡b ext corr zero (s-chain (I←B i0 i1) prf b←q 0-chain)                                      = refl
    kc-shrink-≡b ext corr zero (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain)           = refl
    kc-shrink-≡b ext corr zero (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) = refl
    -- Inductive case
    kc-shrink-≡b ext corr (suc ()) (s-chain (I←B i0 i1) prf b←q 0-chain) 
    kc-shrink-≡b ext corr (suc ()) (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain) 
    kc-shrink-≡b ext corr (suc i) (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) 
      = kc-shrink-≡b ext corr i c

    -- Lastly, the locked-round-rule has a similar proof. Not interfering with
    -- quorum certs preserves the invariant trivially.
    locked-round : (ext : ExtendsB bt cb) → ValidBT bt 
                 → LockedRound (insert-block bt cb ext)
    locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
      with ValidBT.locked-round-rule valid {R} α hα 
                   {q} {rc-shrink ext (ValidBT.correct valid) {q} rc} 
                   {n} (kc-shrink ext (ValidBT.correct valid) c3) 
                   va 
                   {q'} (rc-shrink ext (ValidBT.correct valid) {q'} rc') 
                   va' hyp
    ...| r = subst₂ _≤_ (cong Abs.bRound (kc-shrink-≡b ext (ValidBT.correct valid) (suc (suc zero)) c3)) 
                        (sym (rc-shrink-prevRound ext (ValidBT.correct valid) {q'} rc')) 
                        r

    valid : (ext : ExtendsB bt cb) → ValidBT bt → ValidBT (insert-block bt cb ext)
    valid ext v = valid-bt (correct ext (ValidBT.correct v)) 
                           (incr-round ext v) 
                           (votes-once ext v) 
                           (locked-round ext v)

  -- *** Insertion of QCs
 
  -- I'm parametrizing over bt and cb, but can't really put ExtendsB in here
  -- since we often need to pattern-match over it.
  module InsertQCLemmas (bt : BlockTree)(vqc : Σ QuorumCert IsValidQC) where
    open WithRSS

    stable : (ext : ExtendsQC bt vqc) → {r : Abs.Record}
                     → r ∈BT bt
                     → r ∈BT (insert-qc bt vqc ext)
    stable ext {Abs.I}   r∈bt                     = unit
    stable (extends m (Q _ prf) o) {Abs.B x} r∈bt = r∈bt
    stable (extends m (Q _ prf) o) {Abs.Q x} r∈bt 
      with lookup (Abs.qCertBlockId x) (_btIdToQuorumCert bt)
         | inspect (lookup (Abs.qCertBlockId x)) (_btIdToQuorumCert bt)
    ...| nothing | _     = ⊥-elim r∈bt
    ...| just γq | [ R ]
      rewrite lookup-stable {k' = Abs.qCertBlockId x} {v' = vqc} prf R
        = r∈bt

    -- Inserting QCs does not interfere with _btIdToBlock
    no-interf : (ext : ExtendsQC bt vqc)
              → _btIdToBlock (insert-qc bt vqc ext)
              ≡ _btIdToBlock bt
    no-interf (extends _ (Q _ _) _) = refl

    -- If a record was not in bt, but is in (insert cb bt), said record must
    -- be the inserted one. Differntly than blocks though, here we can only
    -- prove that the latest insertion certifies the same block, but might
    -- not be /exactly/ the same. 
    target : (ext : ExtendsQC bt vqc)
           → {r : Abs.Record}
           → ¬ (r ∈BT bt)
           → r ∈BT (insert-qc bt vqc ext)
           → ∃[ q ] (r ≡ Abs.Q q × Abs.qCertBlockId q ≡ Abs.qCertBlockId (α-QC vqc)
                                 × Abs.qRound q ≡ Abs.qRound (α-QC vqc))
    target ext {Abs.I}   neg hyp = ⊥-elim (neg hyp)
    target ext {Abs.B x} neg hyp 
      rewrite no-interf ext = ⊥-elim (neg hyp) 
    target ext@(extends {r' = Abs.Q x'} m (Q q0 prf) (B←Q b1 b2)) {Abs.Q x} neg hyp 
      with lookup (Abs.qCertBlockId x) (_btIdToQuorumCert (insert-qc bt vqc ext))
         | inspect (lookup (Abs.qCertBlockId x)) (_btIdToQuorumCert (insert-qc bt vqc ext))
    ...| nothing | _     = ⊥-elim hyp
    ...| just γq | [ R ]
      with insert-target prf (λ abs → neg (maybe-lift ((x ≋QC_) ∘ α-QC) hyp abs)) R 
    ...| refl , refl = x , refl , refl , proj₂ hyp

    -- The inserted record is an element of the update blocktree.
    elem : (ext : ExtendsQC bt vqc) → Abs.Q (α-QC vqc) ∈BT insert-qc bt vqc ext
    elem (extends rInPool (Q res notThere) x) 
      rewrite lookup-correct {k = Abs.qCertBlockId (α-QC vqc)} 
                             {v = vqc} 
                             {kvm = bt ^∙ btIdToQuorumCert} 
                             notThere 
            = refl , refl

    -- Inserting in a correct blocktree yeilds a correct blocktree.
    correct : (ext : ExtendsQC bt vqc) → Correct bt → Correct (insert-qc bt vqc ext)
    correct ext cbt s s∈post 
      with s ∈BT? bt 
    ...| yes s∈bt = rc-grow (λ {r} r∈bt → stable ext {r} r∈bt) (cbt s s∈bt)
    ...| no  s∉bt 
      with target ext {s} s∉bt s∈post 
    ...| (q , refl , refl , refl) 
      with ext
    ...| e@(extends {r = r} a canI (B←Q refl refl))
       = step {r' = Abs.Q q}
              (rc-grow (λ {r} r∈bt → stable (extends a canI (B←Q refl refl)) {r} r∈bt) (cbt r a)) 
              (B←Q refl refl) {elem e}

{-
    locked-round : (ext : ExtendsQC bt vqc) → ValidBT bt 
                 → LockedRound (insert-qc bt vqc ext)
    locked-round ext valid {R} α hα {q} {rc} {n} c2 va {q'} rc' va' hyp = {!!}
-}


{-
       = WithRSS.step (rc-grow (stable (extends a canI r←r')) (cbt r a)) 
                      r←r' {elem (extends a canI r←r')}
-}


--   
--   insert-ok-correct rss r' ext vrss s s∈post 
--     with s ∈BT? rss
--   ...| yes s∈rss = rc-grow (insert-stable ext) (ValidBT.correct vrss s s∈rss)
--   ...| no  s∉rss 
--     rewrite insert-target ext s∉rss s∈post 
--     with ext
--   ...| extends {r = r} a b r←r' 
--      = WithBT.step (rc-grow (insert-stable {rss} (extends a b r←r')) 
--                                       (ValidBT.correct vrss r a))
--                     r←r' {insert-∈BT (extends a b r←r')}

    
  ---------------------
  -- IS CORRECT RULE --

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


{-

    with <M$>-univ α-Block (lookup (Abs.bId x) (_btIdToBlock bt)) r∈bt
  ...| (lkupRes , isJust , αres)
    rewrite lookup-stable {k' = Abs.bId x} {v' = cb} prf isJust 
          = cong just αres
    = r∈bt
-}

{-
    with <M$>-univ (_qcCertifies ∘ proj₁) 
                   (lookup (Abs.qCertBlockId x) (_btIdToQuorumCert bt)) r∈bt
  ...| (lkupRes , isJust , αres)
    rewrite lookup-stable {k' = Abs.qCertBlockId x} {v' = cb} prf {!isJust!}
          = {!!}
-}
  

{-
  insert-block bt ab (extends rInPool (B b abdGood idAvail) x)
    = record bt { _btIdToBlock = kvm-insert (Abs.bId ab) b 
                                        (_btIdToBlock bt) idAvail}

  insert-qc : ∀ (bt : BlockTree)(aq : Abs.QC)
               → (ext : Extends bt (Abs.Q aq))
               → BlockTree
  insert-qc bt aq (extends rInPool (Q {_} {cqm} _ idAvail) x)
    = record bt { _btIdToQuorumCert = kvm-insert (Abs.qCertBlockId aq) cqm 
                                             (_btIdToQuorumCert bt) idAvail}

  insert-init  : ∀ (bt : BlockTree)(ext : Extends bt Abs.I)
               → BlockTree
  insert-init  bt (extends _ () _)

  insert : ∀ (bt : BlockTree)(r' : Abs.Record)(ext : Extends bt r')
         → BlockTree
  insert bt  Abs.I    ext = insert-init bt ext
  insert bt (Abs.B b) ext = insert-block bt b ext
  insert bt (Abs.Q q) ext = insert-qc bt q ext
-}

{-
  insert-stable ext {Abs.I} b = unit

  -- TODO: eliminate warnings -- unsolved meta.  Key is that Blocks don't extend Blocks
  --       and QCs don't extend QCs.
  insert-stable {bt} (extends _ (B _ _) _) {Abs.Q ()}
  insert-stable {bt} (extends _ (Q _ _) _) {Abs.B ()}

  -- MSM: can't help feeling I overcomplicated these proofs
  insert-stable {bt} (extends _ (B _ idAvail) _) {Abs.B ab} hyp
    with         (lookup (Abs.bId ab)) (_btIdToBlock bt) |
         inspect (lookup (Abs.bId ab)) (_btIdToBlock bt)
  ...| nothing | _ = ⊥-elim (maybe-⊥ hyp refl)
  ...| just lb | [ xx ] =
         subst ((_≡ just ab) ∘ (α-Block <M$>_))
               (sym (lookup-stable-1 idAvail xx))
               (trans (cong (α-Block <M$>_) xx) hyp)

  insert-stable {bt} (extends _ (Q _ idAvail) _) {Abs.Q aq} hyp
    with         (lookup (Abs.qCertBlockId aq)) (_btIdToQuorumCert bt) |
         inspect (lookup (Abs.qCertBlockId aq)) (_btIdToQuorumCert bt)
  ...| nothing | _ = ⊥-elim (maybe-⊥ hyp refl)
  ...| just qcp | [ xx ] =
         subst ((_≡ just (Abs.qCertBlockId aq)) ∘ ((_qcCertifies ∘ proj₁) <M$>_))
               (sym (lookup-stable-1 idAvail xx))
               (trans (cong (((_qcCertifies ∘ proj₁) <M$>_)) xx) hyp)

-}
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
--   ...| yes s∈rss = rc-grow (insert-stable ext) (ValidBT.correct vrss s s∈rss)
--   ...| no  s∉rss 
--     rewrite insert-target ext s∉rss s∈post 
--     with ext
--   ...| extends {r = r} a b r←r' 
--      = WithBT.step (rc-grow (insert-stable {rss} (extends a b r←r')) 
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


