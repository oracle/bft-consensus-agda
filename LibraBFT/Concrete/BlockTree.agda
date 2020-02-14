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
  import LibraBFT.Concrete.Records.Valid ec as Meta

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
  α-Block b' with b' ^∙ lbExecutedBlock ∙ ebBlock
  ...| b with b ^∙ bBlockData ∙ bdBlockType
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

  α-Vote : (qc : QuorumCert)(valid : Meta.IsValidQC qc) 
         → ∀ {as}
         → as ∈ qcVotes qc
         → Abs.Vote
  α-Vote qc v {author , sig , ord} as∈QC = record
    { vAuthor   = Meta.ivaIdx (All-lookup (Meta.ivqcValidAuthors v) as∈QC)
    ; vBlockUID = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; vRound    = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
    ; vOrder    = unsafeReadMeta ord -- VCM: here's the cliff hanger! if we just
                                     --      ord in here Agda will reject.
    }

  α-QC : Σ QuorumCert Meta.IsValidQC → Abs.QC
  α-QC (qc , valid) = record
    { qCertBlockId = qc ^∙ qcVoteData ∙ vdProposed ∙ biId
    ; qRound       = qc ^∙ qcVoteData ∙ vdProposed ∙ biRound
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


  {- MSM: I remain unconvinced that a) the invariant implied above currently holds, and b) that even if it
     does, it's a good idea to bake in the assumption that it will continue to hold.  Despite the
     commentary above, there is a path in which a block gets added to btIdToBlock even though the QC
     it contains is not added to btIdToQuorumCert (on that path), as follows (line numbers are
     relative to commit 4db7f78 in hospital repo):

     * A new proposal is received, and passed to processProposalMsgM (EventProcessor.hs, line 129)
     * It is passed to preProcessProposalM (line 137)
     * All checks in preProcessProposalM pass, and we call syncUpM (line 159)
     * The conditions at lines 317-319 all pass, so syncUpM returns True.
     * This means that syncUpM does *not* call SyncManager.syncToM (line 326) and therefore does not
       call insertSingleQuorumCertM (SyncManager.hs, line 25), which is the only way the QC will be
       inserted into btIdToQuorumCert.
     * because syncUpM returned True, we call ProposerElection.processProposalM (EventProcessor.hs,
       line 160) to confirm the proposer is the correct one for the round, in which case processProposalM
       returns a just Block (ProposerElection.hs, line 25), and therefore so does preProcessProposalM
     * Therefore processProposedBlockM is called (EventProcessor.hs, line 137), the checks at lines
       183-186 pass, so executeAndVoteM is called (line 188), which calls
       BlockStore.executeAndInsertBlockM (line 226), and the block is inserted (BlockStore.hs, line 65)

     IF the alleged invariant holds, it is because the conditions at lines 317-319 mentioned above
     ensure that the QC embedded in the to-be-added block is *already* in btIdToQuorumCert.  This is
     far from clear to me.

     Questions/comments:

     - Maybe it is OK that we don't consider the QC embedded in the inserted block to be ∈BT the
       blockstore in this case, so the definition of _∈BT_ can remain the same even though the
       invariant doesn't hold.  This would be OK if we would never use that QC in attempting to
       commit.  We'd have to prove that, and there is some cognitive overhead for having ∈BT differ
       from intuition.

     - As discussed before, we can have a definition of ∈BT that allows a QC to be either in
       btIdToQuorumCert or in a block in btIdToBlock (we keep proof irrelevance by preferring on and
       using the other only if the QC is not in the preferred one).  Yes, it complicates the
       definition a bit, but it avoids the issues mentioned above, so I think we should keep it in
       mind.

     - Finally, we need to understand where QCs come from that are used for committing, because
       those are the ones that we need to be ∈BT in order to invoke properties of the abstract model
       to establish Correctness.  It's not necessarily as simple as being in one or other of these
       two maps.  We need to understand in detail what verification is done by both leaders and
       followers when committing.  Here are some (incomplete, not well organized) notes...

       - SafetyRules.constructLedgerInfoM determines whether the proposed block establishes a new
         3-chain, and if so includes commit information in the LedgerInfo, which is included in the
         vote constructed for the proposed block (see EventProcessor.hs, lines 188 and 231, and
         SafetyRules.hs, lines 51 and 69-81).

       - pathFromRootM gets blocks to commit (both for leader and followers), only from btIdToBlock,
         so these are all ∈BT.  It uses the QC embedded in one block to determine the id of the
         previous block.  This does *not* imply that the QC is ∈BT with our current definition, but
         it trivially would if we used the more inclusive (and slightly more complicated) definition
         of ∈BT for QCs, which would consider a QC embedded in a block in the btIdToBlock map to be
         ∈BT.

       - Leaders and followers both commit via processCertificatesM, followers via
         preProcessProposalM and syncUpM, leaders via newQcAggregatedM after adding a vote that
         forms a new QC.

       - Generating new proposals:
         - generateProposalM (ProposalGenerator.hs)
         - QC included is from bsHighestQuorumCert (lines 42-49)
         - which is set only in BlockTree.hs, insertQuorumCertM line 97 (note that
           bsHighestquorumcert is just a "lens" to btHighestQuorumCert)
         - which of course also ensures that the QC is ∈BT (line 99)
         - however, it seems that the proposer does *not* put the proposed block in its btIdToBlock map
         - our current prototype broadcasts the proposal to all (presumably including self, so it
           gets into the leader's block store that way)
         - thus the only way blocks are added to the block store is as described above
         - in the case of a leader adding its own proposal, the QC it contains is already in btIdToQuorumCert
           before it broadcasts the proposal 
         - thus the only threat to the invariant posited above is the case above (involving lines 317-319)
           for a follower
         - having dug a little further, now I understand that the condition on line 319 says that we have
           already committed up to/past the round number of the *previous block* (i.e., the one that the
           embedded QC certifies); I have to dig further to understand how this impacts this discussion.
           Does it mean that there is already *some* QC that certifies the previous block in btIdToQuorumCert,
           so our alleged invariant holds?  Or maybe it doesn't matter in this case, and we could weaken
           the invariant?

  -}

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


-- TODO: Update this for new refined structure that matches the Haskell types

--   _∈BT_ : {a : Set} → Abs.Record → BlockTree a → Set
--   Abs.I     ∈BT bt = Unit -- The initial record is not really *in* the record store,
--   (Abs.B b) ∈BT bt 
--     = α-Block <M$> (lookup (Abs.bId b) (btIdToBlock bt)) ≡ just b
--   (Abs.Q q) ∈BT bt 
--     -- A qc is said to be in the abstract state iff there exists
--     -- a qc that certifies the same block (i.e., with the same id).
--     -- We don't particularly care for the list of votes or who authored it
--     = (qcCertifies ∘ proj₁) <M$> (lookup (Abs.qCertBlockId q) (btIdToQuorumCert bt)) 
--       ≡ just (Abs.qCertBlockId q)

--   _∈BT?_ : (r : Abs.Record)(bt : BlockTree) → Dec (r ∈BT bt)
--   Abs.I     ∈BT? bt = yes unit
--   (Abs.B b) ∈BT? bt 
--     with lookup (Abs.bId b) (btIdToBlock bt)
--   ...| nothing = no (λ x → maybe-⊥ refl (sym x))
--   ...| just r  
--     with α-Block r Abs.≟Block b
--   ...| yes refl = yes refl
--   ...| no  ok   = no (ok ∘ just-injective)
--   (Abs.Q q) ∈BT? bt = {!!}

--   ∈BT-irrelevant : ∀{r rss}(p₀ p₁ : r ∈BT rss) → p₀ ≡ p₁
--   ∈BT-irrelevant {Abs.I} unit unit    = refl
--   ∈BT-irrelevant {Abs.B x} {st} p0 p1 = ≡-irrelevant p0 p1
--   ∈BT-irrelevant {Abs.Q x} {st} p0 p1 = ≡-irrelevant p0 p1

--   instance
--     abstractBT : isRecordStoreState BlockTree
--     abstractBT = record
--       { isInPool            = _∈BT_
--       ; isInPool-irrelevant = ∈BT-irrelevant 
--       }

--   --------------------
--   -- The Invariants --
--   --------------------

--   Correct : BlockTree → Set
--   Correct st = AbstractI.Correct st

--   IncreasingRound : BlockTree → Set
--   IncreasingRound st = AbstractI.IncreasingRoundRule st

--   VotesOnlyOnce : BlockTree → Set
--   VotesOnlyOnce st = AbstractI.VotesOnlyOnceRule st

--   LockedRound : BlockTree → Set₁
--   LockedRound st = AbstractI.LockedRoundRule st

--   -- A Valid Record Store State is one where all
--   -- the invariants are respected.
--   record ValidBT (bt : BlockTree) : Set₁ where
--     constructor valid-bt
--     field
--       correct           : Correct bt
--       incr-round-rule   : IncreasingRound bt
--       votes-once-rule   : VotesOnlyOnce bt
--       locked-round-rule : LockedRound bt

--   ---------------------
--   -- The Empty State --
--   ---------------------

  -- TODO: fill out other fields
  emptyBT : BlockTree
  emptyBT = record
    { btIdToBlock      = empty
    ; btIdToQuorumCert = empty
    }

--   empty-Correct : Correct emptyBT
--   empty-Correct Abs.I     _    = WithRSS.empty
--   empty-Correct (Abs.B b) imp
--     = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ (α-Block <M$>_))
--                                  (sym (kvm-empty {k = Abs.bId b}))
--                                  refl))
--   empty-Correct (Abs.Q q) imp
--     = ⊥-elim (maybe-⊥ imp (subst ((_≡ nothing) ∘ ((qcCertifies ∘ proj₁) <M$>_))
--                                  (sym (kvm-empty {k = Abs.qCertBlockId q}))
--                                  refl))

--   empty-IncreasingRound : IncreasingRound emptyBT
--   empty-IncreasingRound α x {q = q} x₁ x₂ va va' x₃
--     = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ ((qcCertifies ∘ proj₁) <M$>_))
--                                  (sym (kvm-empty {k = Abs.qCertBlockId q}))
--                                  refl))

--   empty-VotesOnlyOnce : VotesOnlyOnce emptyBT
--   empty-VotesOnlyOnce α x {q = q} x₁ x₂ va va' x₃
--     = ⊥-elim (maybe-⊥ x₁ (subst ((_≡ nothing) ∘ ((qcCertifies ∘ proj₁) <M$>_))
--                                  (sym (kvm-empty {k = Abs.qCertBlockId q}))
--                                  refl))


--   empty-LockedRound : LockedRound emptyBT
--   empty-LockedRound _ _ _ _ (WithRSS.step {r' = Abs.Q q'} _ _ {abs}) _ _
--     = ⊥-elim (maybe-⊥ abs (subst ((_≡ nothing) ∘ ((qcCertifies ∘ proj₁) <M$>_))
--                                  (sym (kvm-empty {k = Abs.qCertBlockId q'}))
--                                  refl))


--   -- And now this is really trivial
--   emptyBT-valid : ValidBT emptyBT
--   emptyBT-valid =
--     valid-bt empty-Correct
--              empty-IncreasingRound
--              empty-VotesOnlyOnce
--              empty-LockedRound

-- {-

--   --------------------------------
--   -- Semantically Valid Records --

--   abstractRecord : Record → Maybe Abs.Record
--   abstractRecord (B {α} b p1 p2) 
--     with initialAgreedHash ec ≟Hash getPrev b
--   ...| yes _ = just (Abs.B (Abs.mkBlock (hash (encode (content b))) α nothing (getRound b)))
--   ...| no  _ = just (Abs.B (Abs.mkBlock (hash (encode (content b))) α (just (getPrev b)) (getRound b)))
--   abstractRecord (Q b p1 p2) = {!!}
--   abstractRecord _ = nothing

--   -- A record extends some other in a state if there exists
--   -- a record chain in said state that ends on the record supposed
--   -- to be extended
--   data Extends (rss : RecordStoreState) : Abs.Record → Set where
--      -- VCM: We might carry more information on this constructor
--      extends : ∀{r r'}
--              → (rInPool : r ∈BT rss)
--              -- We will not allow insertion of a Record whose hash
--              -- collides with one already in the RecordStore.
--              -- Otherwise we'll have to carry HashBroke around on
--              -- most/all properties.
--              -- → (r'New : lookup (rssPool rss) (hashR r') ≡ nothing)
--              → (r'New : ¬ (r' ∈BT rss))
--              → r ← r'
--              → Extends rss r'
-- {-
--   extends-Q? : (rss : RecordStoreState)(q : QC)
--              → lookup (rssPool rss) (hashRecord (Q q)) ≡ nothing
--              → Maybe (Extends rss (Q q))
--   extends-Q? rss q ok
--     -- Structure is similar to extends-B? below, which is commented in detail.
--     with lookup (rssPool rss) (getPrevHash q)
--        | inspect (lookup (rssPool rss)) (getPrevHash q)
--   ...| nothing    | [ _ ] = nothing
--   ...| just (I _) | [ _ ] = nothing
--   ...| just (Q _) | [ _ ] = nothing
--   ...| just (B b) | [ R ]
--      with getRound q ≟ getRound b
--   ...| no _ = nothing
--   ...| yes round-ok = just (extends (lookup-∈HS _ _ R) ok
--                              (B←Q {b} round-ok (sym (lookup-correct _ _ R))))

--   extends-B? : (rss : RecordStoreState)(b : Block)
--              → lookup (rssPool rss) (hashRecord (B b)) ≡ nothing
--              → Maybe (Extends rss (B b))
--   extends-B? rss b ok
--   -- 1. Are we extending the initial record?
--     with getPrevHash b ≟Hash hashRecord (I mkInitial)
--   ...| yes refl with 1 ≤? getRound b
--   ...| yes xx = just (extends {r = I mkInitial} unit ok
--                                 (I←B xx refl))
--   ...| no _   = nothing
--   extends-B? rss b ok
--      | no  ¬Init
--   -- 2. Ok, if not the initial, which one? We must look it up.
--     with lookup (rssPool rss) (getPrevHash b)
--        | inspect (lookup (rssPool rss)) (getPrevHash b)
--   -- 2.1 case nothing was found, it does not extend.
--   ...| nothing | [ R ] = nothing
--   -- 2.2 case we found the initial contradicts the check at (1)
--   ...| just (I mkInitial) | [ R ]
--      = ⊥-elim (¬Init (lookup-correct (getPrevHash b) (rssPool rss) R))
--   -- 2.3 case we found a block, it does not extend. Blocks only extend QC's
--   ...| just (B _) | [ R ] = nothing
--   -- 2.4 case we found a QC, it might extend
--   ...| just (Q q) | [ R ]
--   -- 2.4.1 Is block round strictly greater than the QC it extends?
--      with suc (getRound q) ≤? getRound b
--   -- 2.4.1.1 No; the rounds are not ok.
--   ...| no round-nok = nothing
--   -- 2.4.1.2 Yes, rounds are fine; So far, it extends.
--   --         VCM: Shouldn't we perform additional checks?
--   ...| yes round-ok = just (extends (lookup-∈HS _ _ R) ok
--                              (Q←B {q} round-ok (sym (lookup-correct _ _ R))))

--   -- This shows how we can construct an Extends record, as the concrete model will need to do.
--   -- However, it only produces a Maybe Extends, wnich could be satisfied by alway returning nothing.
--   -- We could level-up by making this a Dec (Extends rss r), showing that we can construct an
--   -- Extends rss r or there isn't one, thus eliminating this "triviality" concern.
--   extends? : (rss : RecordStoreState)(r : Record) → Maybe (Extends rss r)
--   extends? rss r with (lookup (rssPool rss)) (hashRecord r) | inspect (lookup (rssPool rss)) (hashRecord r)
--   ...| just _  | [ _ ] = nothing -- Cannot insert this record (either it is already in or there is a hash conflict)
--   ...| nothing | [ ok ] with r 
--   ...| I _ = nothing
--   ...| B b = extends-B? rss b ok
--   ...| Q q = extends-Q? rss q ok
-- -}

-- {-
--   open import LibraBFT.Abstract.Records                                  ec 
--   open import LibraBFT.Abstract.BFT                                      ec 
--   open import LibraBFT.Abstract.Records.Extends             hash hash-cr ec 
--   open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
--   open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec

--   hashRecord : Record → Hash
--   hashRecord = hash ∘ encodeR

-- {-
--   ∈BT-correct : (rss : RecordStoreState)(r : Record)
--                → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ just r
--   ∈BT-correct rss (B x) prf = lookup-correct (B x) (rssPool rss) prf
--   ∈BT-correct rss (Q x) prf = lookup-correct (Q x) (rssPool rss) prf

--   ∈BT-correct-⊥ : (rss : RecordStoreState)(r : Record)
--                  → r ∈BT rss → lookup (rssPool rss) (hashRecord r) ≡ nothing → ⊥
--   ∈BT-correct-⊥ = {!!}
-- -}

--   ---------------------------------------
--   -- Honesty and Dishonesty of Authors --

--   data Dishonest (α : Author ec) : Set where
--     same-order-diff-qcs 
--       : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
--       → q ≢ q'
--       → voteOrder (∈QC-Vote q vα) ≡ voteOrder (∈QC-Vote q' vα')
--       → Dishonest α

--   DishonestM : Maybe (Author ec) → Set
--   DishonestM nothing  = ⊥
--   DishonestM (just α) = Dishonest α

--   postulate
--     ACCOUNTABILITY-OPP : ∀{α} → Honest α → Dishonest α → ⊥

--   --------------------------
--   -- Insertion of Records --

--   insert : (rss : RecordStoreState)(r' : Record)(ext : Extends rss r')
--          → RecordStoreState
--   insert rss r' (extends _ nc _) = record rss 
--      {rssPool = hs-insert  r' (rssPool rss) nc
--      }

--   ---------------------
--   -- IS CORRECT RULE --

--   -- We can always inject a record chain from a recordstorestate
--   -- into another by proving the later contains at least all the
--   -- records of the former.
--   RecordChain-grow
--     : {rss rss' : RecordStoreState}{s : Record} 
--     → (∀ {r} → r ∈BT rss → r ∈BT rss')
--     → WithBT.RecordChain rss s → WithBT.RecordChain rss' s
--   RecordChain-grow f WithBT.empty           
--     = WithBT.empty
--   RecordChain-grow f (WithBT.step rc x {p}) 
--     = WithBT.step (RecordChain-grow f rc) x {f p}

--   -- Inserting does not loose any records.
--   insert-stable : {rss : RecordStoreState}{r' : Record}(ext : Extends rss r')
--                 → {r : Record}
--                 → r ∈BT rss
--                 → r ∈BT (insert rss r' ext)
--   insert-stable ext {I x} hyp = unit
--   insert-stable (extends _ nc _) {B x} hyp = hs-insert-stable nc hyp
--   insert-stable (extends _ nc _) {Q x} hyp = hs-insert-stable nc hyp

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
-- -}
