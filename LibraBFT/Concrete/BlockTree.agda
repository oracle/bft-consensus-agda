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
    = (_qcCertifies ∘ proj₁) <M$> (lookup (Abs.qCertBlockId q) (_btIdToQuorumCert bt))
      ≡ just (Abs.qCertBlockId q)

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
  ...| nothing = no λ x → maybe-⊥ refl (sym x)
  ...| just (qq , _) with (_biId (_vdProposed (_qcVoteData qq))) ≟UID Abs.qCertBlockId q
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
    = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ ((_qcCertifies ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))

  empty-IncreasingRound : IncreasingRound emptyBT
  empty-IncreasingRound α x {q = q} x₁ x₂ va va' x₃
    = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ ((_qcCertifies ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))

  empty-VotesOnlyOnce : VotesOnlyOnce emptyBT
  empty-VotesOnlyOnce α x {q = q} x₁ x₂ va va' x₃
    = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ ((_qcCertifies ∘ proj₁) <M$>_))
                                 (sym (kvm-empty {k = Abs.qCertBlockId q}))
                                 refl))


  empty-LockedRound : LockedRound emptyBT
  empty-LockedRound _ _ _ _ (WithRSS.step {r' = Abs.Q q'} _ _ {abs}) _ _
    = ⊥-elim (maybe-⊥ abs (subst ((_≡ nothing) ∘ ((_qcCertifies ∘ proj₁) <M$>_))
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

  -- We can transpose a record chain to a unrelated state
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

    -- Inserting does not lose any records; be it for blocks or QCs
    stable : (ext : ExtendsB bt cb){r : Abs.Record} → r ∈BT bt → r ∈BT (insert-block bt cb ext)
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
    ...| yes s∈bt = RecordChain-grow (stable ext) (cbt s s∈bt)
    ...| no  s∉bt 
      rewrite target ext s∉bt s∈post 
      with ext
    ...| extends {r = r} a canI r←r' 
       = WithRSS.step (RecordChain-grow (stable (extends a canI r←r')) (cbt r a)) 
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

  {-
    -- No QuorumCert in our state can certify a freshly inserted block. 
    nodep : (bt : BlockTree)(cb : LinkableBlock)(ext : ExtendsB bt cb)
                       → ValidBT bt
                       → ∀{q} → (Abs.Q q) ∈BT (insert-block bt cb ext)
                       → Abs.qCertBlockId q ≢ Abs.bId (α-Block cb)
    nodep bt cb ext valid {q} q∈bt abs
      rewrite no-interf {bt} {cb} ext 
      with ext
    ...| extends {Abs.B b} b∈bt canIns (Q←B b0 b1) = ?
  -}
  {-
      with <M$>-univ (_qcCertifies ∘ proj₁) (lookup (Abs.qCertBlockId q) (_btIdToQuorumCert bt)) q∈bt
    ...| ((q' , vq') , r , s) = {!!}
  -}
  {-
      with ext
    ...| extends x (B a b) z rewrite abs = {!!}
  -}

    pres-Q∈BT : (ext : ExtendsB bt cb) 
              → ∀{q} → Abs.Q q ∈BT (insert-block bt cb ext) → Abs.Q q ∈BT bt
    pres-Q∈BT ext hyp = {!!}

    pres-B∈BT : (ext : ExtendsB bt cb)
              → ∀{b} → Abs.B b ∈BT insert-block bt cb ext
              → Abs.bId b ≢ Abs.bId (α-Block cb)
              → Abs.B b ∈BT bt
    pres-B∈BT ext nothd hyp = {!!}

   
    lemma : (ext : ExtendsB bt cb)
          → ∀{q}(rc : WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q))
          → ∀{r} → WithRSS._∈RC_ (insert-block bt cb ext) r rc
          → r ∈BT bt
    lemma ext rc {r} hyp = {!!}

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

    -- If we have a record chain leading to a quorum certificate in the 
    -- state that results from the insertion of a block; we can have the same record chain
    -- wihtout said block.
    rc-shrink : (ext : ExtendsB bt cb) 
              → Correct bt → ∀{q}
              → WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q)
              → WithRSS.RecordChain bt (Abs.Q q)
    rc-shrink ext cor {q} rc = rc-transp rc (λ r∈rc → {!!})
{-
    RecordChain-drop-block ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} rc@(WithRSS.step _ _) (Q←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = WithRSS.step (WithRSS.step (RecordChain-drop-block ext corr {q0} rc) 
                        (Q←B a0 a1) {pres-B∈BT ext {b} b∈bt'
                                      (uncertifiable ext corr {q} q∈bt')}) 
            (B←Q b0 refl) {pres-Q∈BT ext {q} q∈bt'}
    RecordChain-drop-block ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step WithRSS.empty (I←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = WithRSS.step (WithRSS.step WithRSS.empty 
                        (I←B a0 a1) {pres-B∈BT ext {b} b∈bt' 
                                      (uncertifiable ext corr {q} q∈bt')}) 
           (B←Q b0 refl) {pres-Q∈BT ext {q} q∈bt'}


    RecordChain-drop-block-≅ : (ext : ExtendsB bt cb) 
                             → (c   : Correct bt) 
                             → ∀{q}(rc  : WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q))
                             → rc ≅ RecordChain-drop-block ext c rc
    RecordChain-drop-block-≅ ext c (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} rc (Q←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = {!≅-cong₂ (λ P Q → WithRSS.step P (B←Q b0 refl) {Q}) !}
    RecordChain-drop-block-≅ ext c (WithRSS.step {Abs.B b} 
            (WithRSS.step WithRSS.empty (I←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = {!!}


    -- And here is a very complicated way of writing the identity function
    -- on values; yet, reducing these values lets agda undersdant the
    -- relationship between recordchains and 𝕂-chains indexed
    -- over states with and without a freshly inserted block.
    𝕂-chain-drop-block : ∀{R n}(ext : ExtendsB bt cb)
                       → (corr : Correct bt)
                       → ∀{q}{rc : WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q)}
                       → WithRSS.𝕂-chain (insert-block bt cb ext) R n rc 
                       → WithRSS.𝕂-chain bt R n (RecordChain-drop-block ext corr rc)
    𝕂-chain-drop-block ext corr WithRSS.0-chain = WithRSS.0-chain
    𝕂-chain-drop-block ext corr {rc = (WithRSS.step {Abs.B b} 
            (WithRSS.step WithRSS.empty (I←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'})} 
            (WithRSS.s-chain r←b prf b←q WithRSS.0-chain) 
      = WithRSS.s-chain r←b prf b←q WithRSS.0-chain 
    𝕂-chain-drop-block ext corr  {rc = (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} rc (Q←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'})} 
            (WithRSS.s-chain r←b prf b←q k) 
      = WithRSS.s-chain r←b prf b←q (𝕂-chain-drop-block ext corr k) 

    RecordChain-drop-block-cr : (ext : ExtendsB bt cb) 
                              → (corr : Correct bt) → ∀{q}
                              → (rc : WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q))
                              → currRound rc ≡ currRound (RecordChain-drop-block ext corr rc)
    RecordChain-drop-block-cr ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} rc (Q←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = refl
    RecordChain-drop-block-cr ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step WithRSS.empty (I←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = refl

    RecordChain-drop-block-pr : (ext : ExtendsB bt cb) 
                              → (corr : Correct bt) → ∀{q}
                              → (rc : WithRSS.RecordChain (insert-block bt cb ext) (Abs.Q q))
                              → prevRound rc ≡ prevRound (RecordChain-drop-block ext corr rc)
    RecordChain-drop-block-pr ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} (WithRSS.step {r} WithRSS.empty _) (Q←B a0 refl) {b∈bt'}) (B←Q refl refl) {q∈bt'}) 
      = {!refl!}
    RecordChain-drop-block-pr ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step {Abs.Q q0} (WithRSS.step {r} (WithRSS.step _ _) _) (Q←B a0 refl) {b∈bt'}) (B←Q refl refl) {q∈bt'}) 
      = {!refl!}
    RecordChain-drop-block-pr ext corr {q} (WithRSS.step {Abs.B b} 
            (WithRSS.step WithRSS.empty (I←B a0 a1) {b∈bt'}) (B←Q b0 refl) {q∈bt'}) 
      = refl


    -- Lastly, the locked-round-rule has a similar proof. Not interfering with
    -- quorum certs preserves the invariant trivially.
    locked-round : (ext : ExtendsB bt cb) → ValidBT bt → LockedRound (insert-block bt cb ext)
    locked-round ext valid {R} α hα {q} {rc} {n} c2 va {q'} rc' va' hyp 
      -- rewrite no-interf ext 
      with ValidBT.locked-round-rule valid {R} α hα 
                   {q} {RecordChain-drop-block ext (ValidBT.correct valid) {q} rc} 
                   {n} (𝕂-chain-drop-block ext (ValidBT.correct valid) c2) 
                   va 
                   {q'} (RecordChain-drop-block ext (ValidBT.correct valid) {q'} rc') 
                   va' hyp
    ...| r = subst₂ _≤_ {!!} {!!} r

-}

  -- *** Insertion of QCs

  insert-qc-stable : (bt : BlockTree)(vqc : Σ QuorumCert IsValidQC)(ext : ExtendsQC bt vqc)
                   → {r : Abs.Record}
                   → r ∈BT bt
                   → r ∈BT (insert-qc bt vqc ext)
  insert-qc-stable bt qc ext {Abs.I}   r∈bt                     = unit
  insert-qc-stable bt qc (extends m (Q _ prf) o) {Abs.B x} r∈bt = r∈bt
  insert-qc-stable bt qc (extends m (Q _ prf) o) {Abs.Q x} r∈bt 
    with <M$>-univ (_qcCertifies ∘ proj₁) 
                   (lookup (Abs.qCertBlockId x) (_btIdToQuorumCert bt)) r∈bt
  ...| (lkupRes , isJust , αres) 
    rewrite lookup-stable {k' = Abs.qCertBlockId x} {v' = qc} prf isJust
          = cong just αres


--   
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
