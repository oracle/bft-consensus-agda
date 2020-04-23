{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

-- This module provides the abstraction of a block tree and
-- gives us a insert-qc and insert-block function we should
-- use in our Haskell copy.
module LibraBFT.Concrete.BlockTreeAbstraction
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec      : Meta EpochConfig)
 where

  open import LibraBFT.Concrete.Util.KVMap
    renaming (empty to KV-empty)
  open import LibraBFT.Concrete.NetworkMsg

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
  α-Block b' with ₋ebBlock (₋lbExecutedBlock b')
  ...| b with ₋bdBlockType (₋bBlockData b)
  ...| NilBlock = record
       { bId     = ₋bId b
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
    { vAuthor   = {!!} -- (₋ivaIdx (All-lookup (IsValidQC.₋ivqcValidAuthors v) as∈QC))  -- TODO: this is broken as ₋ivqcValidAuthors has gone way, need to fix
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
    ; qVotes-C2    = subst (_ ≤_) {!!} (IsValidQC.₋ivqcSizeOk valid)
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
    = α-Block <M$> (lookup (Abs.bId b) (₋btIdToBlock bt)) ≡ just b
  (Abs.Q q) ∈BT bt 
    -- A qc is said to be in the abstract state iff there exists
    -- a qc that certifies the same block (i.e., with the same id).
    -- We don't particularly care for the list of votes or who authored it
    = maybe ((q ≋QC_) ∘ α-QC) ⊥ (lookup (Abs.qCertBlockId q) (₋btIdToQuorumCert bt))

  -- It can be useful to open up a `Q q ∈BT bt` hypothesis without having
    -- to do 'with lookup | inspect lookup ...`
  ∈BT-Q-univ : ∀{q bt} → Abs.Q q ∈BT bt
             → ∃[ vqc ] ( lookup (Abs.qCertBlockId q) (₋btIdToQuorumCert bt) ≡ just vqc
                        × q ≋QC (α-QC vqc))
  ∈BT-Q-univ {q} {bt} hyp with lookup (Abs.qCertBlockId q) (₋btIdToQuorumCert bt)
  ...| nothing   = ⊥-elim hyp
  ...| just vqc  = vqc , refl , hyp


  _∈BT?_ : (r : Abs.Record)(bt : BlockTree) → Dec (r ∈BT bt)
  Abs.I     ∈BT? bt = yes unit
  (Abs.B b) ∈BT? bt 
    with lookup (Abs.bId b) (₋btIdToBlock bt)
  ...| nothing = no (λ x → maybe-⊥ refl (sym x))
  ...| just r  
    with α-Block r Abs.≟Block b
  ...| yes refl = yes refl
  ...| no  ok   = no (ok ∘ just-injective)
  (Abs.Q q) ∈BT? bt
    with lookup (Abs.qCertBlockId q) (BlockTree.₋btIdToQuorumCert bt)
  ...| nothing = no id
  ...| just qq = q ≋QC? (α-QC qq)


  ∈BT-irrelevant : ∀{r bt}(p₀ p₁ : r ∈BT bt) → p₀ ≡ p₁
  ∈BT-irrelevant {Abs.I} unit unit    = refl
  ∈BT-irrelevant {Abs.B x} {st} p0 p1 = ≡-irrelevant p0 p1
  ∈BT-irrelevant {Abs.Q x} {st} p0 p1 
    with lookup (Abs.qCertBlockId x) (₋btIdToQuorumCert st)
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
    { ₋btIdToBlock               = KV-empty
    ; ₋btRootId                  = initialAgreedHash (unsafeReadMeta ec)  -- These unsafeReadMetas will go away when
    ; ₋btHighestCertifiedBlockId = initialAgreedHash (unsafeReadMeta ec)  -- we do real epoch changes as these hashes will
    ; ₋btHighestQuorumCert       = {!!} -- ??                             -- come from somewhere else.  Similarly for
    ; ₋btHighestCommitCert       = {!!} -- ??                             -- these initial QCs.
    ; ₋btPendingVotes            = mkPendingVotes KV-empty KV-empty
    ; ₋btPrunedBlockIds          = []
    ; ₋btMaxPrunedBlocksInMem    = 0 
    ; ₋btIdToQuorumCert          = KV-empty
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
      → lookup (Abs.bId cb) (₋btIdToBlock bt) ≡ nothing
      → canInsert bt (Abs.B cb)
    Q : (qc : Abs.QC)
      → lookup (Abs.qCertBlockId qc) (₋btIdToQuorumCert bt) ≡ nothing
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
     = record bt { ₋btIdToBlock = kvm-insert (Abs.bId absCB) cb 
                                         (₋btIdToBlock bt) prf }

  insert-qc : (bt : BlockTree)(qc : Σ QuorumCert IsValidQC)(ext : ExtendsQC bt qc)
            → BlockTree
  insert-qc bt qc (extends rInPool canI x) 
    with α-QC qc | canI
  ...| absQC | Q .absQC prf 
     = record bt { ₋btIdToQuorumCert = kvm-insert (Abs.qCertBlockId absQC) qc
                                              (₋btIdToQuorumCert bt) prf }

  ---------------------------------------
  -- Properties About Valid BlockTrees --

  -- In a valid BlockTree; if a given QC certifies a block, then
  -- such block has a concrete counterpart that belongs in the block tree.
  qc-certifies-closed-conc : (bt : BlockTree) → Correct bt
                           → ∀{q} → (Abs.Q q) ∈BT bt
                           → ∃[ cb ] (lookup (Abs.qCertBlockId q) (₋btIdToBlock bt) ≡ just cb)
  qc-certifies-closed-conc bt correct {q} q∈bt 
    with correct (Abs.Q q) q∈bt
  ...| step {Abs.B b} (step _ _ {b∈bt}) (B←Q refl refl) 
    with <M$>-univ α-Block (lookup (Abs.bId b) (₋btIdToBlock bt)) b∈bt
  ...| (cb , inThere , _) = cb , inThere

  -- The tail of a record chain is always an element of the state.
  rc-∈BT : {bt : BlockTree}{r : Abs.Record}
         → RecordChain bt r → r ∈BT bt
  rc-∈BT empty            = unit
  rc-∈BT (step _ _ {prf}) = prf

  -- Properties about insert-block
  module _ (bt : BlockTree)(cb : LinkableBlock) where

    insert-block-stable : (ext : ExtendsB bt cb){r : Abs.Record} 
                        → r ∈BT bt → r ∈BT (insert-block bt cb ext)
    insert-block-stable _                       {Abs.I}   r∈bt = unit
    insert-block-stable (extends m (B _ prf) o) {Abs.Q x} r∈bt = r∈bt
    insert-block-stable (extends m (B _ prf) o) {Abs.B x} r∈bt 
      with <M$>-univ α-Block (lookup (Abs.bId x) (₋btIdToBlock bt)) r∈bt
    ...| (lkupRes , isJust , αres)
      rewrite lookup-stable {k' = Abs.bId x} {v' = cb} prf isJust 
            = cong just αres

    -- Inserting blocks does not interfere with ₋btIdToQuorumCert
    insert-block-no-interf : (ext : ExtendsB bt cb)
                           → ₋btIdToQuorumCert (insert-block bt cb ext)
                           ≡ ₋btIdToQuorumCert bt
    insert-block-no-interf (extends _ (B _ _) _) = refl

    -- If a record was not in bt, but is in (insert cb bt), said record must
    -- be the inserted one.
    insert-block-target : (ext : ExtendsB bt cb)
                        → {r : Abs.Record}
                        → ¬ (r ∈BT bt)
                        → r ∈BT (insert-block bt cb ext)
                        → r ≡ Abs.B (α-Block cb)
    insert-block-target ext {Abs.I}   neg hyp = ⊥-elim (neg hyp)
    insert-block-target ext {Abs.Q x} neg hyp 
      rewrite insert-block-no-interf ext = ⊥-elim (neg hyp) 
    insert-block-target ext@(extends m (B _ prf) o) {Abs.B x} neg hyp 
      with <M$>-univ α-Block (lookup (Abs.bId x) (₋btIdToBlock (insert-block bt cb ext))) hyp 
    ...| (lkupRes , isJust , refl) 
      with insert-target prf (λ { x → neg (cong (α-Block <M$>_) x) }) isJust
    ...| _ , refl  = refl

    -- The inserted record is an element of the update blocktree.
    insert-block-elem : (ext : ExtendsB bt cb) → Abs.B (α-Block cb) ∈BT insert-block bt cb ext
    insert-block-elem (extends rInPool (B res notThere) x) 
      rewrite lookup-correct {k = Abs.bId (α-Block cb)} 
                             {v = cb} 
                             {kvm = bt ^∙ btIdToBlock} 
                             notThere 
            = refl

    -- Inserting in a correct blocktree yeilds a correct blocktree.
    insert-block-correct : (ext : ExtendsB bt cb) → Correct bt → Correct (insert-block bt cb ext)
    insert-block-correct ext cbt s s∈post 
      with s ∈BT? bt 
    ...| yes s∈bt = rc-grow (λ {r} r∈bt → insert-block-stable ext {r} r∈bt) (cbt s s∈bt)
    ...| no  s∉bt 
      rewrite insert-block-target ext {s} s∉bt s∈post 
      with ext
    ...| extends {r = r} a canI r←r' 
       = step (rc-grow (λ {r₀} r₀∈bt → insert-block-stable (extends a canI r←r') {r₀} r₀∈bt) (cbt r a)) 
              r←r' {insert-block-elem (extends a canI r←r')}

    -- The proof for increasing round rule is easy; insert-block does
    -- not interfere with quorum certificates.
    insert-block-incr-round : (ext : ExtendsB bt cb) → ValidBT bt → IncreasingRound (insert-block bt cb ext)
    insert-block-incr-round ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp
      -- Both QC's must be old; since we just inserted a block. 
      rewrite insert-block-no-interf ext
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    ...| no imp   | _         = ⊥-elim (imp q∈bt)
    ...| yes qOld | no  imp   = ⊥-elim (imp q'∈bt)
    ...| yes qOld | yes q'Old = ValidBT.incr-round-rule valid α hα {q} {q'} qOld q'Old va va' hyp

    -- Same for votes-only-once; there is no interference with quorum certificates
    insert-block-votes-once : (ext : ExtendsB bt cb) → ValidBT bt → VotesOnlyOnce (insert-block bt cb ext)
    insert-block-votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp
      -- Both QC's must be old; since we just inserted a block. 
      rewrite insert-block-no-interf ext
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    ...| no imp   | _         = ⊥-elim (imp q∈bt)
    ...| yes qOld | no  imp   = ⊥-elim (imp q'∈bt)
    ...| yes qOld | yes q'Old = ValidBT.votes-once-rule valid α hα {q} {q'} qOld q'Old va va' hyp

    -- ** The Odyssey of the LockedRound **

    -- VCM: We can make Abstract.RecrodChain.∈RC.transp heterogeneous
    -- but it will break the proofs below; For now, I'll leave ∈RC homogeneous
    -- and keep te proofs. If the implemenation and the system either require or,
    -- indeed, give us wha we need on a plate, I'll come back around.

    insert-block-pres-Q∈BT 
      : (ext : ExtendsB bt cb) 
      → ∀{q} → Abs.Q q ∈BT (insert-block bt cb ext) → Abs.Q q ∈BT bt
    insert-block-pres-Q∈BT ext hyp rewrite insert-block-no-interf ext = hyp

    insert-block-pres-B∈BT 
      : (ext : ExtendsB bt cb)
      → ∀{b} → Abs.B b ∈BT insert-block bt cb ext
      → Abs.bId b ≢ Abs.bId (α-Block cb)
      → Abs.B b ∈BT bt
    insert-block-pres-B∈BT ext@(extends _ (B _ x) _) {b} hyp nothd
      with <M$>-univ α-Block (lookup (Abs.bId b) (₋btIdToBlock (insert-block bt cb ext))) hyp
    ...| (bb , isJust , refl) 
      rewrite lookup-stable-2 x isJust nothd = refl

    -- A freshly inserted block is uncertifiable; in other words, for any
    -- quorum certificaet that belongs in (insert-block bt cb ext), said QC 
    -- cant certify cb.
    insert-block-uncertifiable 
      : (ext : ExtendsB bt cb)
      → Correct bt
      → ∀{q} → Abs.Q q ∈BT insert-block bt cb ext
      → Abs.qCertBlockId q ≢ Abs.bId (α-Block cb)
    insert-block-uncertifiable ext correct {q} q∈bt' refl
      with qc-certifies-closed-conc bt correct {q} (insert-block-pres-Q∈BT ext {q} q∈bt')
    ...| (_ , cb∈bt) 
      with ext
    ...| extends _ (B _ cbNew) _ = maybe-⊥ cb∈bt cbNew

    mutual
     insert-block-is-not-cb 
       : (ext : ExtendsB bt cb) → Correct bt
       → ∀{b}(rc : RecordChain (insert-block bt cb ext) (Abs.B b))
       → Abs.bId b ≢ Abs.bId (α-Block cb)
       → ∀{r} → r ∈RC rc
       → r ∈BT bt
     insert-block-is-not-cb ext cor rc hyp (transp {_} {rc₀} old eq) 
       = insert-block-is-not-cb ext cor rc₀ hyp old
     insert-block-is-not-cb ext@(extends _ (B αbt btNew) _) cor {b} (step rc _ {prf}) hyp (here) 
       with <M$>-univ α-Block (lookup (Abs.bId b) (₋btIdToBlock (insert-block bt cb ext))) prf
     ...| (lb , isthere , refl) 
       rewrite lookup-stable-2 btNew isthere hyp 
             = refl
     insert-block-is-not-cb ext cor (empty ↜[ b∈bt ] I←B i0 i1) hyp (there p x {prf}) 
       rewrite ∈RC-empty-I x = unit
     insert-block-is-not-cb ext cor (rc ↜[ b∈bt ] Q←B q0 q1)    hyp (there p x {prf}) 
       = insert-block-doesnt-use-cb ext cor rc x

     insert-block-doesnt-use-cb 
       : (ext : ExtendsB bt cb) → Correct bt
       → ∀{q}(rc : RecordChain (insert-block bt cb ext) (Abs.Q q))
       → ∀{r} → r ∈RC rc
       → r ∈BT bt
     insert-block-doesnt-use-cb ext cor rc (transp {_} {rc₀} old eq) 
       = insert-block-doesnt-use-cb ext cor rc₀ old
     insert-block-doesnt-use-cb ext cor (step _ _ {q∈bt'}) {r} (here) 
       rewrite insert-block-no-interf ext = q∈bt'
     insert-block-doesnt-use-cb ext cor {q} (rc ↜[ q∈bt' ] B←Q b0 b1) {r} (there p x {prf})
       = insert-block-is-not-cb ext cor rc (λ h → insert-block-uncertifiable ext cor {q} prf (trans (sym b1) h)) x

    -- If we have a record chain leading to a quorum certificate in the 
    -- state that results from the insertion of a block; we can have the same record chain
    -- wihtout said block.
    --
    -- We need this because we need to explain to Agda that any RecordChain
    -- that ends in a QC can't reference the newly inserted block. This is useful
    -- to call our invariants inductively
    insert-block-rc-shrink 
      : (ext : ExtendsB bt cb) 
      → Correct bt → ∀{q}
      → RecordChain (insert-block bt cb ext) (Abs.Q q)
      → RecordChain bt (Abs.Q q)
    insert-block-rc-shrink ext cor rc = rc-transp rc (insert-block-doesnt-use-cb ext cor rc)

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
    insert-block-rc-shrink-prevRound
      : (ext : ExtendsB bt cb)(cor : Correct bt)
      → ∀{q}(rc : RecordChain (insert-block bt cb ext) (Abs.Q q)) 
      → prevRound rc ≡ prevRound (insert-block-rc-shrink ext cor rc)
    insert-block-rc-shrink-prevRound ext cor (step (step rc (I←B _ _)) (B←Q _ refl))         = refl
    insert-block-rc-shrink-prevRound ext cor (step (step (step _ _) (Q←B _ _)) (B←Q _ refl)) = refl

    -- Here, for instance, we need to go over the elements of the k-chain
    -- simply to let Agda reduce rc-shrink (patter matching on the k-chain
    -- yeilds info about the shabe of the recordchain, which in turn, reduces rc-shrink)
    insert-block-kc-shrink 
      : ∀{R n}(ext : ExtendsB bt cb)
      → (corr : Correct bt)
      → ∀{q}{rc : RecordChain (insert-block bt cb ext) (Abs.Q q)}
      → 𝕂-chain (insert-block bt cb ext) R n rc 
      → 𝕂-chain bt R n (insert-block-rc-shrink ext corr rc)
    insert-block-kc-shrink ext cor 0-chain = 0-chain
    insert-block-kc-shrink ext cor (s-chain (I←B i0 i1) prf b←q 0-chain) 
      = s-chain (I←B i0 i1) prf b←q 0-chain
    insert-block-kc-shrink ext cor (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain) 
      = s-chain (Q←B q0 q1) prf (B←Q b0 refl) 0-chain
    insert-block-kc-shrink ext cor (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) 
      = s-chain (Q←B q0 q1) prf (B←Q b0 refl) (insert-block-kc-shrink ext cor {q'} c) 

    -- We should be able to "easily" prove that kc-shrink does /not/
    -- alter the blocks of the kchain.
    insert-block-kc-shrink-≡b : ∀{R n}(ext : ExtendsB bt cb)
                 → (corr : Correct bt)
                 → ∀{q}{rc : RecordChain (insert-block bt cb ext) (Abs.Q q)}
                 → (i : Fin n)
                 → (kc : 𝕂-chain (insert-block bt cb ext) R n rc)
                 → kchainBlock i (insert-block-kc-shrink ext corr kc) ≡ kchainBlock i kc
    insert-block-kc-shrink-≡b ext corr () 0-chain
    -- Base case; easy byt requires to match on a lot of stuff to reduce kc-shrink
    insert-block-kc-shrink-≡b ext corr zero (s-chain (I←B i0 i1) prf b←q 0-chain)                                      = refl
    insert-block-kc-shrink-≡b ext corr zero (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain)           = refl
    insert-block-kc-shrink-≡b ext corr zero (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) = refl
    -- Inductive case
    insert-block-kc-shrink-≡b ext corr (suc ()) (s-chain (I←B i0 i1) prf b←q 0-chain) 
    insert-block-kc-shrink-≡b ext corr (suc ()) (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@0-chain) 
    insert-block-kc-shrink-≡b ext corr (suc i) (s-chain {r = Abs.Q q'} (Q←B q0 q1) prf (B←Q b0 refl) c@(s-chain _ _ _ _)) 
      = insert-block-kc-shrink-≡b ext corr i c

    -- Lastly, the locked-round-rule has a similar proof. Not interfering with
    -- quorum certs preserves the invariant trivially.
    insert-block-locked-round : (ext : ExtendsB bt cb) → ValidBT bt 
                              → LockedRound (insert-block bt cb ext)
    insert-block-locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
      with ValidBT.locked-round-rule valid {R} α hα 
                   {q} {insert-block-rc-shrink ext (ValidBT.correct valid) {q} rc} 
                   {n} (insert-block-kc-shrink ext (ValidBT.correct valid) c3) 
                   va 
                   {q'} (insert-block-rc-shrink ext (ValidBT.correct valid) {q'} rc') 
                   va' hyp
    ...| r = subst₂ _≤_ (cong Abs.bRound (insert-block-kc-shrink-≡b ext (ValidBT.correct valid) (suc (suc zero)) c3)) 
                        (sym (insert-block-rc-shrink-prevRound ext (ValidBT.correct valid) {q'} rc')) 
                        r

    insert-block-valid : (ext : ExtendsB bt cb) → ValidBT bt → ValidBT (insert-block bt cb ext)
    insert-block-valid ext v = valid-bt (insert-block-correct ext (ValidBT.correct v)) 
                                        (insert-block-incr-round ext v) 
                                        (insert-block-votes-once ext v) 
                                        (insert-block-locked-round ext v)


  -- Properties about insert-qc
  module _ (bt : BlockTree)(vqc : Σ QuorumCert IsValidQC) where

    insert-qc-stable : (ext : ExtendsQC bt vqc) → {r : Abs.Record}
                     → r ∈BT bt
                     → r ∈BT (insert-qc bt vqc ext)
    insert-qc-stable ext {Abs.I}   r∈bt                     = unit
    insert-qc-stable (extends m (Q _ prf) o) {Abs.B x} r∈bt = r∈bt
    insert-qc-stable (extends m (Q _ prf) o) {Abs.Q x} r∈bt 
      with lookup (Abs.qCertBlockId x) (₋btIdToQuorumCert bt)
         | inspect (lookup (Abs.qCertBlockId x)) (₋btIdToQuorumCert bt)
    ...| nothing | _     = ⊥-elim r∈bt
    ...| just γq | [ R ]
      rewrite lookup-stable {k' = Abs.qCertBlockId x} {v' = vqc} prf R
        = r∈bt

    -- Inserting QCs does not interfere with ₋btIdToBlock
    insert-qc-no-interf : (ext : ExtendsQC bt vqc)
                        → ₋btIdToBlock (insert-qc bt vqc ext)
                        ≡ ₋btIdToBlock bt
    insert-qc-no-interf (extends _ (Q _ _) _) = refl

    -- If a record was not in bt, but is in (insert cb bt), said record must
    -- be the inserted one. Differntly than blocks though, here we can only
    -- prove that the latest insertion certifies the same block, but might
    -- not be /exactly/ the same. 
    insert-qc-target : (ext : ExtendsQC bt vqc)
                     → {r : Abs.Record}
                     → ¬ (r ∈BT bt)
                     → r ∈BT (insert-qc bt vqc ext)
                     → ∃[ q ] (r ≡ Abs.Q q × Abs.qCertBlockId q ≡ Abs.qCertBlockId (α-QC vqc)
                                           × Abs.qRound q ≡ Abs.qRound (α-QC vqc))
    insert-qc-target ext {Abs.I}   neg hyp = ⊥-elim (neg hyp)
    insert-qc-target ext {Abs.B x} neg hyp 
      rewrite insert-qc-no-interf ext = ⊥-elim (neg hyp) 
    insert-qc-target ext@(extends {r' = Abs.Q x'} m (Q q0 prf) (B←Q b1 b2)) {Abs.Q x} neg hyp 
      with lookup (Abs.qCertBlockId x) (₋btIdToQuorumCert (insert-qc bt vqc ext))
         | inspect (lookup (Abs.qCertBlockId x)) (₋btIdToQuorumCert (insert-qc bt vqc ext))
    ...| nothing | _     = ⊥-elim hyp
    ...| just γq | [ R ]
      with insert-target prf (λ abs → neg (maybe-lift ((x ≋QC_) ∘ α-QC) hyp abs)) R 
    ...| refl , refl = x , refl , refl , proj₂ hyp

    -- The inserted record is an element of the update blocktree.
    insert-qc-elem : (ext : ExtendsQC bt vqc) → Abs.Q (α-QC vqc) ∈BT insert-qc bt vqc ext
    insert-qc-elem (extends rInPool (Q res notThere) x) 
      rewrite lookup-correct {k = Abs.qCertBlockId (α-QC vqc)} 
                             {v = vqc} 
                             {kvm = bt ^∙ btIdToQuorumCert} 
                             notThere 
            = refl , refl

    -- Easier to use version of 'target'
    insert-qc-univ : (ext : ExtendsQC bt vqc){r : Abs.Record}
                   → r ∈BT insert-qc bt vqc ext
                   → (∃[ q ] (r ≡ Abs.Q q × q ≋QC (α-QC vqc))) ⊎ r ∈BT bt
    insert-qc-univ ext {r} r∈bt with r ∈BT? bt
    ...| yes res  = inj₂ res
    ...| no  rOld with insert-qc-target ext {r} rOld r∈bt
    ...| (q , corr , id≡ , r≡) = inj₁ (q , corr , id≡ , r≡)

    -- Inserting in a correct blocktree yeilds a correct blocktree.
    insert-qc-correct : (ext : ExtendsQC bt vqc) → Correct bt → Correct (insert-qc bt vqc ext)
    insert-qc-correct ext cbt s s∈post 
      with s ∈BT? bt 
    ...| yes s∈bt = rc-grow (λ {r} r∈bt → insert-qc-stable ext {r} r∈bt) (cbt s s∈bt)
    ...| no  s∉bt 
      with insert-qc-target ext {s} s∉bt s∈post 
    ...| (q , refl , refl , refl) 
      with ext
    ...| e@(extends {r = r} a canI (B←Q refl refl))
       = step {r' = Abs.Q q}
              (rc-grow (λ {r} r∈bt → insert-qc-stable (extends a canI (B←Q refl refl)) {r} r∈bt) (cbt r a)) 
              (B←Q refl refl) {insert-qc-elem e}


{-
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

-}
