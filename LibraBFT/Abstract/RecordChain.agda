open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Abstract.RecordStoreState 

module LibraBFT.Abstract.RecordChain 
  (ec  : Meta EpochConfig)
  (UID : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  {a}{ST : Set a}⦃ isST : isRecordStoreState ec UID _≟UID_ ST ⦄ 
    where

 open import LibraBFT.Abstract.Records          ec UID _≟UID_
 open import LibraBFT.Abstract.Records.Extends  ec UID _≟UID_

 IsInPool : Record → ST → Set
 IsInPool r = isInPool isST r

 IsInPool-irrelevant : ∀{st r}(p₀ p₁ : IsInPool st r) → p₀ ≡ p₁
 IsInPool-irrelevant = isInPool-irrelevant isST

 -- One way of looking at a 'RecordChain r' is to think of it as 
 -- one path from the epoch's initial record to r. This path, however,
 -- depends on a state. A record chain will only use records from
 -- the same state.
 data RecordChain (st : ST) : Record → Set where
   empty : RecordChain st I
   step  : ∀ {r r'}
         → (rc : RecordChain st r) 
         → r ← r'
         → {prf : IsInPool r' st} -- TODO: Make these into instance arguments too!
         → RecordChain st r'

 -- This is a helpful syntax for talking about record chains
 infix 30 step
 syntax step rc r←r' {prf} = rc ↜[ prf ] r←r'

 prevBlock : ∀{st q} → RecordChain st (Q q) → Block
 prevBlock (step {r = B b} _ (B←Q _ _)) = b

 -- Defition of 'previous_round' as in Paper Section 5.5
 currRound : ∀{st r} → RecordChain st r → Round
 currRound empty = 0
 currRound (step {r = r} _ _) = round r

 -- TODO: prev round should be defined for blocks only...
 prevRound : ∀{st r} → RecordChain st r → Round
 prevRound empty = 0
 prevRound (step rc (I←B x vr)) = 0
 prevRound (step rc (Q←B x vr)) = currRound rc
 prevRound (step rc (B←Q x vr)) = prevRound rc

 ----------------------
 -- RecordChain Equality and Irrelevance
 --

 -- Distributing a record relation pointwise
 -- over record chains. Let rc₀ and rc₁ be as illustrated
 -- below; a value of type ≈RC-pw, named prf is shown
 -- in between them.
 -- 
 --  rc₀    : B₀ ← C₀  ← B₁ ← C₁ ← ⋯ ← Bₖ  ← Cₖ
 --
 --  prf      ≈    ≈     ≈    ≈        ≈     ≈
 --
 --  rc₁    : 𝓑₀ ← 𝓒₀ ← 𝓑₁ ← 𝓒₁ ← ⋯ ← 𝓑ₖ ← 𝓒ₖ
 --
 --
 data ≈RC-pw {ℓ}(_≈_ : Rel Record ℓ){st₀ st₁} 
     : ∀{r₀ r₁} → RecordChain st₀ r₀ → RecordChain st₁ r₁ → Set ℓ where
   eq-empty : I ≈ I → ≈RC-pw _≈_ empty empty
   eq-step  : ∀{r₀ r₁ s₀ s₁}
            → (rc₀ : RecordChain st₀ s₀)
            → (rc₁ : RecordChain st₁ s₁)
            → r₀ ≈ r₁
            → (ext₀ : s₀ ← r₀)
            → (ext₁ : s₁ ← r₁)
            → {p₀ : IsInPool r₀ st₀}
            → {p₁ : IsInPool r₁ st₁}
            → ≈RC-pw _≈_ rc₀ rc₁
            → ≈RC-pw _≈_ (step rc₀ ext₀ {p₀}) (step rc₁ ext₁ {p₁})

 -- RecordChain equivalence is then defined in terms of
 -- record equivalence (i.e., we don't care about the set of
 -- votes for the QCs in the chain); borrowing the illustration
 -- above, we now have:
 --
 --  rc₀    : B₀ ← C₀  ← B₁ ← C₁ ← ⋯ ← Bₖ  ← Cₖ
 --
 --  prf      ≡    ≈QC   ≡    ≈QC      ≡     ≈QC
 --
 --  rc₁    : 𝓑₀ ← 𝓒₀ ← 𝓑₁ ← 𝓒₁ ← ⋯ ← 𝓑ₖ ← 𝓒ₖ
 --
 -- It is easy to see that if rc₀ ≈RC rc₁, then they contain
 -- the same blocks (propositionally!) but potentially 
 -- different /sets of votes/ certifying said blocks.
 _≈RC_ : ∀{st₀ st₁ r₀ r₁} → RecordChain st₀ r₀ → RecordChain st₁ r₁ → Set
 _≈RC_ = ≈RC-pw _≈Rec_

 -- Heterogeneous irrelevance of _≈RC_ happens only modulo
 -- propositional non-injectivity of block ids; which is
 -- awesome!
 ≈RC-refl : ∀{st₀ st₁ r₀ r₁}(rc₀ : RecordChain st₀ r₀)(rc₁ : RecordChain st₁ r₁)
          → r₀ ≈Rec r₁
          → NonInjective _≡_ bId ⊎ (rc₀ ≈RC rc₁)
 ≈RC-refl empty empty hyp 
    = inj₂ (eq-empty hyp)
 ≈RC-refl (step r0 x) (step r1 x₁) hyp 
    = (←-≈Rec x x₁ hyp ⊎⟫= ≈RC-refl r0 r1)
       ⊎⟫= (inj₂ ∘ eq-step r0 r1 hyp x x₁)
 ≈RC-refl empty (step r1 (I←B x x₁)) () 
 ≈RC-refl empty (step r1 (Q←B x x₁)) () 
 ≈RC-refl empty (step r1 (B←Q x x₁)) () 
 ≈RC-refl (step r0 (I←B x x₁)) empty () 
 ≈RC-refl (step r0 (Q←B x x₁)) empty () 
 ≈RC-refl (step r0 (B←Q x x₁)) empty () 

 -- Heterogeneous irrelevance is easy to conjure and pretty interesting, it
 -- proves that two record chains that end up in the same record
 -- have the same blocks and equivalent QCs.
 RecordChain-irrelevant : ∀{st₀ st₁ r}(rc₀ : RecordChain st₀ r)(rc₁ : RecordChain st₁ r) 
                        → NonInjective _≡_ bId ⊎ rc₀ ≈RC rc₁
 RecordChain-irrelevant rc0 rc1 = ≈RC-refl rc0 rc1 ≈Rec-refl

 ---------------------------
 -- RecordChain Operations

 -- We can always inject a record chain from a recordstorestate
 -- into another by proving the later contains at least all the
 -- records of the former.
 rc-grow : {st st' : ST}{s : Record}
         → (∀ {r} → IsInPool r st → IsInPool r st')
         → RecordChain st s → RecordChain st' s
 rc-grow f empty                   = empty
 rc-grow f (step {_} {r} rc x {p}) = step (rc-grow (λ {r₀} → f {r₀}) rc) x {f {r} p}

 -- Growing a record chain doesn't alter its records.
 rc-grow-≈ : ∀{st st' s}(st⊆st' : ∀{r} → IsInPool r st → IsInPool r st')
           → (rc : RecordChain st s)
           → rc ≈RC rc-grow st⊆st' rc
 rc-grow-≈ f empty = eq-empty eq-I
 rc-grow-≈ f (step rc x) = eq-step rc (rc-grow f rc) ≈Rec-refl x x (rc-grow-≈ f rc)

 --------------------------
 -- RecordChain elements

 -- States that a given record belongs in a record chain.
 data _∈RC_ (r₀ : Record){st} : ∀{r₁} → RecordChain st r₁ → Set a where
   here   : ∀{rc : RecordChain st r₀} → r₀ ∈RC rc
   there  : ∀{r₁ r₂}{rc : RecordChain st r₁}(p : r₁ ← r₂)
          → r₀ ∈RC rc
          → {prf : IsInPool r₂ st}
          → r₀ ∈RC (step rc p {prf})
   -- This is a very important rule! It is the equivalent of a
   -- /congruence/ on record chains and enables us to prove
   -- the 𝕂-chain-∈RC property, which is crucial, since we
   -- lost the ability to rewrite record chains
   transp : ∀{r}{rc₀ : RecordChain st r}{rc₁ : RecordChain st r}
          → r₀ ∈RC rc₀ → rc₀ ≈RC rc₁ → r₀ ∈RC rc₁
          -- VCM: we could have tranp relate record chains over two
          -- different states, but that causes issues I don't want to
          -- deal with in the concrete module; while there is no explicit
          -- need for this, I'll hold back this generalization.

 -- More useful than rc-grow is transporting a record chain
 -- solely based on its records. This is almost like a subst
 -- for record chains.
 --
 -- A record chain will be defined in terms of a BlockTree,
 -- when we modify this BlockTree by inserting blocks or QCs, we need 
 -- to "transport" record chains that were cast in terms of the /old/ BlockTree
 -- to be cast in terms of the /new/ bt. No magic here, this is just
 -- dependent-types boilerplate. The diagram below illustrates this.
 --
 --
 --     bt                   I <- B <- Q <- B1 <- QC1 <- B2 <- QC2 <- B3
 --                          ⌞₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋⌟
 --      |                            rc : RecordChain bt B2
 --      |
 --      |
 --      v
 --
 --  insert-qc bt     I <- B <- Q <- B1 <- QC1 <- B2 <- QC2 <- B3 <- QC3
 --                   ⌞₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋⌟
 --                            rc-transp rc ⋯ : RecordChain (insert-qc bt) B2
 --
 --
 -- We can transport a record chain to a unrelated state
 -- as long as all of its records are in there.
 rc-transp : {st st' : ST}{s : Record}
           → (rc : RecordChain st s) 
           → (∀{r} → r ∈RC rc → IsInPool r st')
           → RecordChain st' s
 rc-transp empty f = empty
 rc-transp (step rc x {p}) f 
   = step (rc-transp rc (λ r∈rc → f (there x r∈rc))) x {f here}

 -- As expected, transporting a record chain preserves its records.
 rc-transp-≈ : {st st' : ST}{s : Record}
             → (rc : RecordChain st s) 
             → (f : ∀{r} → r ∈RC rc → IsInPool r st')
             → rc ≈RC rc-transp rc f
 rc-transp-≈ empty f = eq-empty eq-I
 rc-transp-≈ (step rc x) f = eq-step rc (rc-transp rc (λ r∈rc → f (there x r∈rc)))
                                        ≈Rec-refl x x 
                                        (rc-transp-≈ rc (λ r∈rc → f (there x r∈rc)))

 -- A k-chain (paper Section 5.2) is a sequence of
 -- blocks and quorum certificates for said blocks:
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₖ ← Cₖ
 --
 -- Our datatype 𝕂-chain captures exactly that structure.
 --
 data 𝕂-chain (st : ST)(R : Record → Record → Set)
     : (k : ℕ){r : Record} → RecordChain st r → Set where
   0-chain : ∀{r}{rc : RecordChain st r} → 𝕂-chain st R 0 rc
   s-chain : ∀{k r}{rc : RecordChain st r}{b : Block}{q : QC}
           → (r←b : r   ← B b)
           → {prfB : IsInPool (B b) st}
           → (prf : R r (B b))
           → (b←q : B b ← Q q)
           → {prfQ : IsInPool (Q q) st}
           → 𝕂-chain st R k rc
           → 𝕂-chain st R (suc k) ((rc ↜[ prfB ] r←b) ↜[ prfQ ] b←q)

 -- Simple 𝕂-chains do not impose any restricton on its records.
 Simple : Record → Record → Set
 Simple _ _ = Unit

 -- Contiguous 𝕂-chains are those that have contiguous rounds.
 Contig : Record → Record → Set
 Contig r r' = round r' ≡ suc (round r)

 𝕂-chain-contig : (st : ST)(k : ℕ){r : Record} → RecordChain st r → Set
 𝕂-chain-contig st = 𝕂-chain st Contig

 -- Every record chain that ends in a QC is a 𝕂-chain
 to-kchain : ∀{st q}(rc : RecordChain st (Q q)) → ∃[ k ] (𝕂-chain st Simple k rc)
 to-kchain (step (step {B b} rc ()) x@(B←Q _ _)) 
 to-kchain (step (step {I} rc x₁)   x@(B←Q _ _)) 
  = 1 , s-chain x₁ unit x 0-chain
 to-kchain (step (step {Q q} rc x₁) x@(B←Q _ _)) 
  with to-kchain rc
 ...| k , kc = suc k , s-chain x₁ unit x kc

 kchainForget : ∀{st P k r}{rc : RecordChain st r}(c : 𝕂-chain st P k rc) → RecordChain st r
 kchainForget {rc = rc} _ = rc

 -- Returns the round of the block heading the k-chain.
 kchainHeadRound : ∀{st k r P}{rc : RecordChain st r} → 𝕂-chain st P k rc → Round
 kchainHeadRound (0-chain {r = r})      = round r
 kchainHeadRound (s-chain r←b _ b←q kk) = kchainHeadRound kk

 kchainBlock : ∀{st k r P}{rc : RecordChain st r} → Fin k → 𝕂-chain st P k rc → Block
 kchainBlock zero    (s-chain {b = b} _ _ _ _) = b
 kchainBlock (suc x) (s-chain r←b _ b←q kk)    = kchainBlock x kk

 _b⟦_⟧ : ∀{st k r P}{rc : RecordChain st r} → 𝕂-chain st P k rc → Fin k → Block
 chain b⟦ ix ⟧ = kchainBlock ix chain

 kchainQC : ∀{st k r P}{rc : RecordChain st r} → Fin k → 𝕂-chain st P k rc → QC
 kchainQC zero    (s-chain {q = q} _ _ _ _) = q
 kchainQC (suc x) (s-chain r←b _ b←q kk)    = kchainQC x kk

 kchain-to-RecordChain-at-b⟦⟧
   : ∀{st P k r}{rc : RecordChain st r}(c : 𝕂-chain st P k rc)(ix : Fin k)
   → RecordChain st (B (c b⟦ ix ⟧))
 kchain-to-RecordChain-at-b⟦⟧ 0-chain ()
 kchain-to-RecordChain-at-b⟦⟧ (s-chain {rc = rc} r←b {pb} x b←q {pq} c) zero
   = (step rc r←b {pb})
 kchain-to-RecordChain-at-b⟦⟧ (s-chain r←b x b←q c) (suc zz)
   = kchain-to-RecordChain-at-b⟦⟧ c zz

 kchainBlockRoundZero-lemma
   : ∀{st k q P}{rc : RecordChain st (Q q)}(c : 𝕂-chain st P (suc k) rc)
   → getRound (kchainBlock zero c) ≡ getRound q
 kchainBlockRoundZero-lemma (s-chain r←b prf (B←Q r h) c) = sym r

 kchainBlockRound≤ : ∀{st k r P}{rc : RecordChain st r}(x y : Fin k)(kc : 𝕂-chain st P k rc)
                   → x ≤Fin y → getRound (kchainBlock y kc) ≤ getRound (kchainBlock x kc)
 kchainBlockRound≤ zero zero (s-chain r←b prf b←q kc) hyp = ≤-refl
 kchainBlockRound≤ zero (suc y) (s-chain (Q←B r r←b) prf b←q (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc)) hyp 
   = ≤-trans (kchainBlockRound≤ zero y (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc) z≤n) (<⇒≤ r)
 kchainBlockRound≤ (suc x) (suc y) (s-chain r←b prf b←q kc) (s≤s hyp) 
   = kchainBlockRound≤ x y kc hyp

 kchain-round-≤-lemma'
   : ∀{st k q}{rc : RecordChain st (Q q)}(c3 : 𝕂-chain st Contig k rc)(ix : Fin k)
   → getRound (c3 b⟦ ix ⟧) ≤ getRound q
 kchain-round-≤-lemma' (s-chain r←b x (B←Q refl b←q) c3) zero = ≤-refl
 kchain-round-≤-lemma' (s-chain (I←B prf imp) refl (B←Q refl _) 0-chain) (suc ()) 
 kchain-round-≤-lemma' (s-chain (Q←B prf imp) x (B←Q refl _) c2) (suc ix) 
   = ≤-trans (kchain-round-≤-lemma' c2 ix) (≤-unstep prf)

 rc-←-maxRound : ∀{st r r'}(rc : RecordChain st r') → r ∈RC rc → round r ≤ round r'
 rc-←-maxRound rc here                 = ≤-refl
 rc-←-maxRound rc (transp n x)         = rc-←-maxRound _ n
 rc-←-maxRound .(step _ p) (there p n) = ≤-trans (rc-←-maxRound _ n) (←-round-≤ p)

 ∈RC-empty-I : ∀{st r} → r ∈RC (empty  {st = st}) → r ≡ I
 ∈RC-empty-I here                      = refl
 ∈RC-empty-I (transp old (eq-empty x)) = ∈RC-empty-I old

 kchainBlock-correct
   : ∀{st P k q b}{rc : RecordChain st (B b)}{b←q : B b ← Q q}{ipq : IsInPool (Q q) st}
   → (kc : 𝕂-chain st P k (step rc b←q {ipq}))
   → (x : Fin k) → (B (kc b⟦ x ⟧)) ∈RC rc
 kchainBlock-correct (s-chain r←b prf b←q kc) zero = here 
 kchainBlock-correct (s-chain r←b prf b←q (s-chain r←b₁ prf₁ b←q₁ kc)) (suc x) 
   = there r←b (there b←q₁ (kchainBlock-correct (s-chain r←b₁ prf₁ b←q₁ kc) x))

 -- This is an extended form of RecordChain-irrelevance.
 -- Let rc be:
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₙ ← Cₙ
 -- 
 -- The (c : 𝕂-chain P k rc) is a predicate on the shape
 -- of rc, estabilishing it must be of the following shape:
 -- (where consecutive blocks satisfy P!)
 --
 --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₙ₋ₖ ← Cₙ₋ₖ ⋯ ← Bₙ₋₁ ← Cₙ₋₁ ← Bₙ ← Cₙ
 --                           /\             /\            /
 --                     ⋯ P ₋⌟  ⌞₋₋₋₋ P ₋₋₋₋⌟  ⌞₋₋₋₋ P ₋₋₋⌟
 --
 -- This property states that for any other record chain
 -- that contains one block b of the kchain above, it also contains
 -- the prefix of the kchain leading to b.
 -- 
 𝕂-chain-∈RC : ∀{st r k P}{rc : RecordChain st r}
             → (c : 𝕂-chain st P k rc)
             → (x y : Fin k)
             → x ≤Fin y
             → {b : Block}(prf : kchainBlock x c ≡ b)
             → (rc₁ : RecordChain st (B b))
             → NonInjective _≡_ bId ⊎ (B (kchainBlock y c) ∈RC rc₁)
 𝕂-chain-∈RC (s-chain r←b {inP} prf b←q c) zero y z≤n refl rc1 
   with RecordChain-irrelevant (step (kchainForget c) r←b {inP}) rc1
 ...| inj₁ hb   = inj₁ hb
 ...| inj₂ res  = inj₂ (transp (kchainBlock-correct (s-chain r←b {inP} prf b←q c) y) res)
 𝕂-chain-∈RC (s-chain r←b prf b←q c) (suc x) (suc y) (s≤s x≤y) hyp rc1 
   = 𝕂-chain-∈RC c x y x≤y hyp rc1

 -----------------
 -- Commit Rule --

 -- A block (and everything preceeding it) is said to match the commit rule
 -- when the block is the head of a contiguious 3-chain. Here we define an auxiliary
 -- datatype to make definitions more bearable.
 data CommitRule (st : ST) : ∀{r} → RecordChain st r → Block → Set where
   commit-rule : ∀{r b}{rc : RecordChain st r}(c3 : 𝕂-chain st Contig 3 rc) 
               → b ≡ c3 b⟦ suc (suc zero) ⟧
               → CommitRule st rc b

 vote≡⇒QPrevHash≡ : {q q' : QC} {v v' : Vote} 
                  → v  ∈ qcVotes q
                  → v' ∈ qcVotes q'
                  → v ≡ v' 
                  → qCertBlockId q ≡ qCertBlockId q'
 vote≡⇒QPrevHash≡ {q} {q'} v∈q v'∈q' refl
     with witness v∈q (qVotes-C3 q) | witness v'∈q' (qVotes-C3 q')
 ... | refl | refl = refl

 vote≡⇒QRound≡ : {q q' : QC} {v v' : Vote} 
               → v  ∈ qcVotes q
               → v' ∈ qcVotes q'
               → v ≡ v' 
               → getRound q ≡ getRound q'
 vote≡⇒QRound≡ {q} {q'} v∈q v'∈q' refl
     with witness v∈q (qVotes-C4 q) | witness v'∈q' (qVotes-C4 q')
 ... | refl | refl = refl

 ¬bRound≡0 : ∀{st b} → RecordChain st (B b) → ¬ (getRound b ≡ 0)
 ¬bRound≡0 (step s (I←B () h)) refl
 ¬bRound≡0 (step s (Q←B () h)) refl
