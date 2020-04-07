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
    -- We might need some system level info!
    -- (sys : ParticularPropertiesOfTheSystemModel)
 where

  open import LibraBFT.Concrete.Util.KVMap
    renaming (empty to KV-empty)
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

  _≋QC?_ : (q q' : Abs.QC) → Dec (q ≋QC q')
  q ≋QC? q' 
    with Abs.qCertBlockId q ≟UID Abs.qCertBlockId q'
  ...| no xx    = no (λ x → xx (proj₁ x))
  ...| yes refl  
    with Abs.qRound q ≟ℕ Abs.qRound q'
  ...| no xx    = no (λ x → xx (proj₂ x))
  ...| yes refl = yes (refl , refl)


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

  -- It can be useful to open up a `Q q ∈BT bt` hypothesis without having
    -- to do 'with lookup | inspect lookup ...`
  ∈BT-Q-univ : ∀{q bt} → Abs.Q q ∈BT bt
             → ∃[ vqc ] ( lookup (Abs.qCertBlockId q) (_btIdToQuorumCert bt) ≡ just vqc
                        × q ≋QC (α-QC vqc))
  ∈BT-Q-univ {q} {bt} hyp with lookup (Abs.qCertBlockId q) (_btIdToQuorumCert bt)
  ...| nothing   = ⊥-elim hyp
  ...| just vqc  = vqc , refl , hyp


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
  ...| just qq = q ≋QC? (α-QC qq)


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

  -- Bring in record-chains for records inside a BlockTree.
  open import LibraBFT.Abstract.RecordChain ec UID _≟UID_ ⦃ abstractBT ⦄

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
    { _btIdToBlock               = KV-empty
    ; :btRootId                  = initialAgreedHash (unsafeReadMeta ec)  -- These unsafeReadMetas will go away when
    ; _btHighestCertifiedBlockId = initialAgreedHash (unsafeReadMeta ec)  -- we do real epoch changes as these hashes will
    ; _btHighestQuorumCert       = {!!} -- ??                             -- come from somewhere else.  Similarly for
    ; _btHighestCommitCert       = {!!} -- ??                             -- these initial QCs.
    ; _btPendingVotes            = mkPendingVotes KV-empty KV-empty
    ; _btPrunedBlockIds          = []
    ; _btMaxPrunedBlocksInMem    = 0 
    ; _btIdToQuorumCert          = KV-empty
    }

  empty-Correct : Correct emptyBT
  empty-Correct Abs.I     _    = empty
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
  empty-LockedRound _ _ _ _ (step {r' = Abs.Q q'} _ _ {abs}) _ _
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
  ...| step {Abs.B b} (step _ _ {b∈bt}) (B←Q refl refl) 
    with <M$>-univ α-Block (lookup (Abs.bId b) (_btIdToBlock bt)) b∈bt
  ...| (cb , inThere , _) = cb , inThere

  -- The tail of a record chain is always an element of the state.
  rc-∈BT : {bt : BlockTree}{r : Abs.Record}
         → RecordChain bt r → r ∈BT bt
  rc-∈BT empty            = unit
  rc-∈BT (step _ _ {prf}) = prf

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

  -----------------------------------------------------------------------------
  -- TEMPORARY: Properties we will need from the syste's layer as postulates --
  -----------------------------------------------------------------------------

  -- VCM: I'm writing postulates for now with the intent of making clear exactly where
  -- the proof is. The idea is that later we can move this postulate to a module parameter
  -- and we know exactly the invariants we need to ensure at the algorithmic level. 


  -- In the vote-order lemma for QCs, I can ulfold and extract information all the way
  -- to having proof that α issued the same voteOrder to vote for two different blocks.
  -- But we also have that α is honest, so this shouldn't be possible.
  --
  -- I'm not too worried about how we plan on putting the pieces together for now.
  -- so I suggest that we keep these postulates as long as we agree that these postulates
  -- represent states and actions that will never be seen or performed by a node running 
  -- our code.
  postulate
    α-BROKE-VOTES-ONCE : ∀{bt α q q'} 
                       → (Abs.Q q) ∈BT bt → (Abs.Q q') ∈BT bt
                       → (va  : α Abs.∈QC q)(va' : α Abs.∈QC q') 
                       → Abs.voteOrder (Abs.∈QC-Vote q va) ≡ Abs.voteOrder (Abs.∈QC-Vote q' va')
                       → Abs.qCertBlockId q ≢ Abs.qCertBlockId q'
                       → ⊥

    α-BROKE-VOTES-INCR : ∀{bt α q q'} 
                       → (Abs.Q q) ∈BT bt → (Abs.Q q') ∈BT bt
                       → (va  : α Abs.∈QC q)(va' : α Abs.∈QC q') 
                       → q ≋QC q'
                       → Abs.voteOrder (Abs.∈QC-Vote q va) < Abs.voteOrder (Abs.∈QC-Vote q' va')
                       → ⊥


  -- ** Properties
  --
  -- *** Insertion of Blocks
 
  -- I'm parametrizing over bt and cb, but can't really put ExtendsB in here
  -- since we often need to pattern-match over it.
  module InsertBlockLemmas (bt : BlockTree)(cb : LinkableBlock) where

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
               → ∀{r} → r ∈RC rc
               → r ∈BT bt
     is-not-cb ext cor rc hyp (transp {_} {rc₀} old eq) 
       = is-not-cb ext cor rc₀ hyp old
     is-not-cb ext@(extends _ (B αbt btNew) _) cor {b} (step rc _ {prf}) hyp (here) 
       with <M$>-univ α-Block (lookup (Abs.bId b) (_btIdToBlock (insert-block bt cb ext))) prf
     ...| (lb , isthere , refl) 
       rewrite lookup-stable-2 btNew isthere hyp 
             = refl
     is-not-cb ext cor (empty ↜[ b∈bt ] I←B i0 i1) hyp (there p x {prf}) 
       rewrite ∈RC-empty-I x = unit
     is-not-cb ext cor (rc ↜[ b∈bt ] Q←B q0 q1)    hyp (there p x {prf}) 
       = doesnt-use-cb ext cor rc x

     doesnt-use-cb : (ext : ExtendsB bt cb) → Correct bt
                   → ∀{q}(rc : RecordChain (insert-block bt cb ext) (Abs.Q q))
                   → ∀{r} → r ∈RC rc
                   → r ∈BT bt
     doesnt-use-cb ext cor rc (transp {_} {rc₀} old eq) 
       = doesnt-use-cb ext cor rc₀ old
     doesnt-use-cb ext cor (step _ _ {q∈bt'}) {r} (here) 
       rewrite no-interf ext = q∈bt'
     doesnt-use-cb ext cor {q} (rc ↜[ q∈bt' ] B←Q b0 b1) {r} (there p x {prf})
       = is-not-cb ext cor rc (λ h → uncertifiable ext cor {q} prf (trans (sym b1) h)) x

    -- If we have a record chain leading to a quorum certificate in the 
    -- state that results from the insertion of a block; we can have the same record chain
    -- wihtout said block.
    --
    -- We need this because we need to explain to Agda that any RecordChain
    -- that ends in a QC can't reference the newly inserted block. This is useful
    -- to call our invariants inductively
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
                 → kchainBlock i (kc-shrink ext corr kc) ≡ kchainBlock i kc
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

    -- Easier to use version of 'target'
    univ : (ext : ExtendsQC bt vqc){r : Abs.Record}
         → r ∈BT insert-qc bt vqc ext
         → (∃[ q ] (r ≡ Abs.Q q × q ≋QC (α-QC vqc)))
         ⊎ r ∈BT bt
    univ ext {r} r∈bt with r ∈BT? bt
    ...| yes res  = inj₂ res
    ...| no  rOld with target ext {r} rOld r∈bt
    ...| (q , corr , id≡ , r≡) = inj₁ (q , corr , id≡ , r≡)

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

    votes-once : (ext : ExtendsQC bt vqc) → ValidBT bt → VotesOnlyOnce (insert-qc bt vqc ext)
    votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
    -- 0. Which of the QC's are present in the pre-state?
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    -- 0.1 Both of them; inductive call.
    ...| yes qOld | yes q'Old 
       = ValidBT.votes-once-rule valid α hα {q} {q'} qOld q'Old va va' hyp
    -- 0.2 Both are new; hence, certifying the same block at the same round;
    --     This means that both votes va and va' have the same vBlockUID and vRound,
    --     the author is the same and their order is the same by hypothesis,
    --     hence, the votes must be the same.
    ...| no  qNew | no  q'New 
      with target ext {Abs.Q q} qNew q∈bt | target ext {Abs.Q q'} q'New q'∈bt
    ...| (γ , refl , refl , refl) | (γ' , refl , refl , refl)
    -- 0.2.0 Albeit painful; we will extract that the blockUID of a vote
    -- is the same as the bCertBlockId from the QC its in
      with witness (Any-lookup-correct va)  (Abs.qVotes-C3 q)
         | witness (Any-lookup-correct va') (Abs.qVotes-C3 q')
    ...| bUID-eq | bUID-eq' 
    -- 0.2.1 Extract round equality
      with witness (Any-lookup-correct va)  (Abs.qVotes-C4 q)
         | witness (Any-lookup-correct va') (Abs.qVotes-C4 q')
    ...| bR-eq | bR-eq' 
      with Any-witness va | Any-witness va'
    ...| bAuthor-eq | bAuthor-eq'
      -- Assemble everything with a fancy congruence
      = Abs.Vote-cong-η (trans bAuthor-eq (sym bAuthor-eq')) 
                        (trans bUID-eq    (sym bUID-eq')) 
                        (trans bR-eq      (sym bR-eq')) 
                        hyp
    -- 0.3 One qc is old, the other has just been inserted; but
    -- this means there is a mismatch in the voteOrders issued by α.
    -- Namelly, with a bit of gymnastics we can extract that
    -- `qCertBlockId q' ≢ qCertBlockId q`, which implies
    -- that `vBlockUID va ≢ `vBlockUID va'`, but `hyp` has type
    -- `voteOrder va ≡ voteOrder va'`, hence, α used the same vote
    -- order to cast votes for different blocks. If α is hones, this can't happen.
    votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | no  qNew | yes q'Old 
      -- AGDA_MAGIC: we need to pass some paramters to this function at this points because
      -- the call to 'target' below will rewrite things; Yet, the last parameter
      -- to this postulate is passed at the very end, 11 lines below.
      with α-BROKE-VOTES-ONCE {insert-qc bt vqc ext} {α} {q} {q'} q∈bt q'∈bt va va' hyp
    ...| α-broke-things
      with target ext {Abs.Q q} qNew q∈bt 
    ...| (.q , refl , refl , refl) 
      with ∈BT-Q-univ {q'} {bt} q'Old
    ...| (vqcOld , isJust , refl , refl) 
      with ext
    ...| e@(extends _ (Q _ notThere) _)
      with Abs.qCertBlockId q ≟Hash Abs.qCertBlockId q'
    ...| yes refl  = ⊥-elim (maybe-⊥ isJust notThere)
    ...| no  q≢q'  = ⊥-elim (α-broke-things q≢q')
    -- 0.4 One qc is old, the other has just been inserted; this
    -- is analogous to 0.3 above, but with q and q' swapped.
    votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | yes qOld | no  q'New 
      with α-BROKE-VOTES-ONCE {insert-qc bt vqc ext} {α} {q} {q'} q∈bt q'∈bt va va' hyp
    ...| α-broke-things
      with target ext {Abs.Q q'} q'New q'∈bt 
    ...| (.q' , refl , refl , refl) 
      with ∈BT-Q-univ {q} {bt} qOld
    ...| (vqcOld , isJust , refl , refl) 
      with ext
    ...| e@(extends _ (Q _ notThere) _)
      with Abs.qCertBlockId q ≟Hash Abs.qCertBlockId q'
    ...| yes refl  = ⊥-elim (maybe-⊥ isJust notThere)
    ...| no  q≢q'  = ⊥-elim (α-broke-things q≢q')

    incr-round : (ext : ExtendsQC bt vqc) → ValidBT bt 
               → IncreasingRound (insert-qc bt vqc ext)
    incr-round ext@(extends _ (Q _ notThere) _) valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
    -- 0. Which of the QC's are present in the pre-state?
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    -- 0.1 Both of them; inductive call.
    ...| yes qOld | yes q'Old 
       = ValidBT.incr-round-rule valid α hα {q} {q'} qOld q'Old va va' hyp
    -- 0.2 None of them; this is impossible because if both
    -- qcs are /the/ new qc; both votes certify the same block, at the
    -- same round but have different voteOrders (per hypothesis).
    ...| no  qNew | no  q'New 
      with target ext {Abs.Q q} qNew q∈bt | target ext {Abs.Q q'} q'New q'∈bt
    ...| (γ , refl , refl , refl) | (γ' , refl , refl , refl)
       = ⊥-elim (α-BROKE-VOTES-INCR {insert-qc bt vqc ext} {α} {q} {q'} 
                                    q∈bt q'∈bt va va' (refl , refl) hyp)
    -- 0.3 Here is where this gets interesting. We are looking at one old and
    -- one new QC; the new one certifies the same block at the same round as vqc (module parm!)
    -- butthe old one was already in the store.
    incr-round ext@(extends _ (Q _ notThere) _) valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | yes qOld | no  q'New 
      with target ext {Abs.Q q'} q'New q'∈bt
    ...| (γ' , refl , refl , refl) = {!!}
    incr-round ext@(extends _ (Q _ notThere) _) valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | no  qNew | yes q'Old 
      with target ext {Abs.Q q} qNew q∈bt
    ...| (γ , refl , refl , refl) = {!!}


    mutual
     is-not-vqc : (ext : ExtendsQC bt vqc) → Correct bt
                → ∀{b}(rc : RecordChain (insert-qc bt vqc ext) (Abs.B b))
                → ∀{r} → r ∈RC rc
                → r ∈BT bt
     is-not-vqc ext cor rc (transp {_} {rc₀} old eq) 
       = is-not-vqc ext cor rc₀ old
     is-not-vqc ext cor rc here with rc-∈BT rc
     ...| res rewrite no-interf ext = res
     is-not-vqc ext cor (empty ↜[ b∈bt ] I←B i0 i1) (there p x {prf}) 
       rewrite ∈RC-empty-I x = unit
     is-not-vqc ext cor (rc ↜[ b∈bt ] Q←B q0 refl)  (there p x {prf}) 
       = doesnt-use-vqc ext cor (λ imp → {!!}) rc x


     doesnt-use-vqc : (ext : ExtendsQC bt vqc) → Correct bt
                    → ∀{q} → Abs.qCertBlockId q ≢ Abs.qCertBlockId (α-QC vqc)
                    → (rc : RecordChain (insert-qc bt vqc ext) (Abs.Q q))
                    → ∀{r} → r ∈RC rc
                    → r ∈BT bt
     doesnt-use-vqc ext cor hyp rc (transp {_} {rc₀} old eq)
        = doesnt-use-vqc ext cor hyp rc₀ old
     doesnt-use-vqc ext cor {q} hyp (step _ _ {q∈bt'}) here
       with univ ext {Abs.Q q} q∈bt'
     ...| inj₁ (.q , refl , abs , _) = ⊥-elim (hyp abs)
     ...| inj₂ res = res
     doesnt-use-vqc ext cor hyp (rc ↜[ q∈bt' ] B←Q b0 refl) {r} (there p x {prf})
        = is-not-vqc ext cor rc x

    rc-shrink : (ext : ExtendsQC bt vqc) 
              → Correct bt → ∀{q}
              → Abs.qCertBlockId q ≢ Abs.qCertBlockId (α-QC vqc)
              → RecordChain (insert-qc bt vqc ext) (Abs.Q q)
              → RecordChain bt (Abs.Q q)
    rc-shrink ext cor hyp rc = rc-transp rc (doesnt-use-vqc ext cor hyp rc)


    locked-round : (ext : ExtendsQC bt vqc) → ValidBT bt 
                 → LockedRound (insert-qc bt vqc ext)
    locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
    -- 0. Which of the QC's are present in the pre-state?
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    -- 0.1 Both of them; inductive call.
    ...| yes qOld | yes q'Old 
       = ValidBT.locked-round-rule valid {R} α hα 
            {q} 
            {rc-shrink ext (ValidBT.correct valid) {!!} rc} {n} 
            {!!} va {q'} 
            (rc-shrink ext (ValidBT.correct valid) {!!} {!rc'!}) va' hyp
    -- 0.2 Impossible; the inserted block is both q and q' but if α is honest,
    -- it abides by the incr-round rule, which means the rounds must be equal.
    -- Yet, hyp has type round q < round q'.
    ...| no  qNew | no  q'New 
      with target ext {Abs.Q q} qNew (rc-∈BT rc) 
         | target ext {Abs.Q q'} q'New (rc-∈BT rc')
    ...| (γ , refl , refl , refl) | (γ' , refl , refl , refl)
       = ⊥-elim (n≮n _ (incr-round ext valid α hα {q} {q'} 
                             (rc-∈BT rc) (rc-∈BT rc') va va' hyp))
    -- We have just inserted q'; in this situation, we need some lemma
    -- that says that since α is honest, it obeys its preferred round and,
    -- we can see its preferred round is at least (getRound (kchainBlock 2 c3))
    locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
       | yes qOld | no  q'New = {!!}
    -- We have just inserted q; seems like we need a similar reasoning to the
    -- case directly above.
    locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
       | no  qNew | yes q'Old = {!!}


 
    -- TODO: Our algorithm will ensure we never cast a vote to a proposal
    -- that references a round smallar than our previous round. We will need
    -- a proof of that. Moreover, we'll later need someway to lift properties
    -- from our own algorithm to another honest author... I need to think carefully
    -- about this.
