open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

-- This module proves that the insertion functions from
-- LibraBFT.Concrete.BlockTreeAbstraction preserve the
-- necessary invariants. This proofs require knowledge of
-- the system layer, hence, I placed them in the Global
-- folder.
module LibraBFT.Global.BlockTreeInvariants
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec      : Meta EpochConfig)
    -- We might need some system level info!
    -- (sys : ParticularPropertiesOfTheSystemModel)
 where

  open import LibraBFT.Concrete.Util.KVMap
    renaming (empty to KV-empty)
  open import LibraBFT.Concrete.NetworkMsg

  open import LibraBFT.Concrete.Consensus.Types.EpochIndep
  open import LibraBFT.Concrete.Consensus.Types.EpochDep ec
  open import LibraBFT.Concrete.BlockTreeAbstraction hash hash-cr ec

  -- Bring in record-chains for records inside a BlockTree.
  open import LibraBFT.Abstract.RecordChain ec UID _≟UID_ ⦃ abstractBT ⦄
  import LibraBFT.Abstract.Records ec UID _≟UID_ as Abs

  -- VCM: I'm starting to realize that the properties votes-once; incr-round
  -- and locked-round are /NOT/ invariants of one state; they are 
  -- invariants of the /system/!
  --
  -- It makes no sense to try framing them as invariants of a single node's
  -- state. I will try working on my smiplified system model branch.

  -- *** Insertion of QCs
 
  -- I'm parametrizing over bt and cb, but can't really put ExtendsB in here
  -- since we often need to pattern-match over it.
  module InsertQCLemmas (bt : BlockTree)(vqc : Σ QuorumCert IsValidQC) where

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
      with insert-qc-target bt vqc ext {Abs.Q q} qNew q∈bt 
         | insert-qc-target bt vqc ext {Abs.Q q'} q'New q'∈bt
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
       | no  qNew | yes q'Old = {!!}
{-
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
-}
    -- 0.4 One qc is old, the other has just been inserted; this
    -- is analogous to 0.3 above, but with q and q' swapped.
    votes-once ext valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | yes qOld | no  q'New = {!!}
{-
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
-}

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
      with insert-qc-target bt vqc ext {Abs.Q q} qNew q∈bt 
         | insert-qc-target bt vqc ext {Abs.Q q'} q'New q'∈bt
    ...| (γ , refl , refl , refl) | (γ' , refl , refl , refl)
       = {!!}
{-
       = ⊥-elim (α-BROKE-VOTES-INCR {insert-qc bt vqc ext} {α} {q} {q'} 
                                    q∈bt q'∈bt va va' (refl , refl) hyp)
-}
    -- 0.3 Here is where this gets interesting. We are looking at one old and
    -- one new QC; the new one certifies the same block at the same round as vqc (module parm!)
    -- butthe old one was already in the store.
    incr-round ext@(extends _ (Q _ notThere) _) valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | yes qOld | no  q'New 
      with insert-qc-target bt vqc ext {Abs.Q q'} q'New q'∈bt
    ...| (γ' , refl , refl , refl) = {!!}
    incr-round ext@(extends _ (Q _ notThere) _) valid α hα {q} {q'} q∈bt q'∈bt va va' hyp 
       | no  qNew | yes q'Old 
      with insert-qc-target bt vqc ext {Abs.Q q} qNew q∈bt
    ...| (γ , refl , refl , refl) = {!!}

{-
    mutual
     is-not-vqc : (ext : ExtendsQC bt vqc) → Correct bt
                → ∀{b}(rc : RecordChain (insert-qc bt vqc ext) (Abs.B b))
                → ∀{r} → r ∈RC rc
                → r ∈BT bt
     is-not-vqc ext cor rc (transp {_} {rc₀} old eq) 
       = is-not-vqc ext cor rc₀ old
     is-not-vqc ext cor rc here with rc-∈BT rc
     ...| res rewrite insert-qc-no-interf ext = res
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
-}

    rc-shrink : (ext : ExtendsQC bt vqc) 
              → Correct bt → ∀{q}
              → Abs.qCertBlockId q ≢ Abs.qCertBlockId (α-QC vqc)
              → RecordChain (insert-qc bt vqc ext) (Abs.Q q)
              → RecordChain bt (Abs.Q q)
    rc-shrink ext cor hyp rc = rc-transp rc {!!} -- (doesnt-use-vqc ext cor hyp rc)


    locked-round : (ext : ExtendsQC bt vqc) → ValidBT bt 
                 → LockedRound (insert-qc bt vqc ext)
    locked-round ext valid {R} α hα {q} {rc} {n} c3 va {q'} rc' va' hyp 
    -- 0. Which of the QC's are present in the pre-state?
      with Abs.Q q ∈BT? bt | Abs.Q q' ∈BT? bt
    -- 0.1 Both of them; inductive call.
    ...| yes qOld | yes q'Old 
       = {!!} {- ValidBT.locked-round-rule valid {R} α hα 
            {q} 
            {rc-shrink ext (ValidBT.correct valid) {!!} rc} {n} 
            {!!} va {q'} 
            (rc-shrink ext (ValidBT.correct valid) {!!} {!rc'!}) va' hyp -}
    -- 0.2 Impossible; the inserted block is both q and q' but if α is honest,
    -- it abides by the incr-round rule, which means the rounds must be equal.
    -- Yet, hyp has type round q < round q'.
    ...| no  qNew | no  q'New 
      with insert-qc-target bt vqc ext {Abs.Q q} qNew (rc-∈BT rc) 
         | insert-qc-target bt vqc ext {Abs.Q q'} q'New (rc-∈BT rc')
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

