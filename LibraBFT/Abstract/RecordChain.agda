open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types

module LibraBFT.Abstract.RecordChain 
  -- A Hash function maps a bytestring into a hash.
  (hash     : ByteString → Hash)
  -- And is colission resistant
  (hash-cr  : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec : EpochConfig)
    where

 open import LibraBFT.Abstract.Records          ec 
 open        WithCryptoHash                     hash hash-cr
 open import LibraBFT.Abstract.Records.Extends  hash hash-cr ec
 open import LibraBFT.Abstract.RecordStoreState hash hash-cr ec

 module WithRSS
   {a}{RSS : Set a}⦃ isRSS : isRecordStoreState RSS ⦄
   -- The current record pool; abstracted by saying
   -- whether a record is in the pool or not.
   (curr : RSS)
     where

  IsInPool : Record → Set
  IsInPool r = isInPool isRSS r curr

  IsInPool-irrelevant : ∀{r}(p₀ p₁ : IsInPool r) → p₀ ≡ p₁
  IsInPool-irrelevant = isInPool-irrelevant isRSS

  -- A record chain is a slice of the reflexive transitive closure with
  -- valid records only. Validity, in turn, is defined by recursion on the
  -- chain.

  -- One way of looking at a 'RecordChain r' is to think of it as 
  -- one path from the epoch's initial record to r.
  data RecordChain : Record → Set where
    empty : RecordChain (I mkInitial)
    step  : ∀ {r r'}
          → (rc : RecordChain r) 
          → r ← r'
          → {prf : IsInPool r'} -- TODO: Make these into instance arguments too!
          → RecordChain r'

  prevBlock : ∀{q} → RecordChain (Q q) → Block
  prevBlock (step {r = B b} _ (B←Q _ _)) = b

  -- Defition of 'previous_round' as in Paper Section 5.5
  currRound : ∀{r} → RecordChain r → Round
  currRound empty = 0
  currRound (step {r = r} _ _) = round r

  -- TODO: prev round should be defined for blocks only...
  prevRound : ∀{r} → RecordChain r → Round
  prevRound empty = 0
  prevRound (step rc (I←B x vr)) = 0
  prevRound (step rc (Q←B x vr)) = currRound rc
  prevRound (step rc (B←Q x vr)) = prevRound rc

  ----------------------
  -- RecordChain Irrelevance
  --
  -- i.e., unless the hash was broken, there is always only
  --       one record chain up to a given record.
  RecordChain-irrelevant : ∀{r}(rc₀ rc₁ : RecordChain r) 
                         → HashBroke ⊎ rc₀ ≡ rc₁
  RecordChain-irrelevant empty empty = inj₂ refl
  RecordChain-irrelevant (step rc0 rc0←r {p0}) (step rc1 rc1←r {p1}) 
    with lemmaS1-2 rc0←r rc1←r 
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl 
    with RecordChain-irrelevant rc0 rc1
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl rewrite ←-irrelevant rc1←r rc0←r 
     = inj₂ (cong (λ Q → step rc0 rc0←r {Q}) 
                  (IsInPool-irrelevant p0 p1))

  -- A k-chain (paper Section 5.2) is a sequence of
  -- blocks and quorum certificates for said blocks:
  --
  --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₖ ← Cₖ
  --
  -- Our datatype 𝕂-chain captures exactly that structure.
  --
  data 𝕂-chain (R : Record → Record → Set) 
      : (k : ℕ){r : Record} → RecordChain r → Set where
    0-chain : ∀{r}{rc : RecordChain r} → 𝕂-chain R 0 rc
    s-chain : ∀{k r}{rc : RecordChain r}{b : Block}{q : QC}
            → (r←b : r   ← B b)
            → {prfB : IsInPool (B b)}
            → (prf : R r (B b))
            → (b←q : B b ← Q q)
            → {prfQ : IsInPool (Q q)}
            → 𝕂-chain R k rc
            → 𝕂-chain R (suc k) (step (step rc r←b {prfB}) b←q {prfQ})

  -- Returns the round of the block heading the k-chain.
  kchainHeadRound : ∀{k r P}{rc : RecordChain r} → 𝕂-chain P k rc → Round
  kchainHeadRound (0-chain {r = r})      = round r
  kchainHeadRound (s-chain r←b _ b←q kk) = kchainHeadRound kk

  kchainBlock : ∀{k r P}{rc : RecordChain r} → Fin k → 𝕂-chain P k rc → Block
  kchainBlock zero    (s-chain {b = b} _ _ _ _) = b
  kchainBlock (suc x) (s-chain r←b _ b←q kk)    = kchainBlock x kk

  _b⟦_⟧ : ∀{k r P}{rc : RecordChain r} → 𝕂-chain P k rc → Fin k → Block
  chain b⟦ ix ⟧ = kchainBlock ix chain

  kchainQC : ∀{k r P}{rc : RecordChain r} → Fin k → 𝕂-chain P k rc → QC
  kchainQC zero    (s-chain {q = q} _ _ _ _) = q
  kchainQC (suc x) (s-chain r←b _ b←q kk)    = kchainQC x kk

  kchainForget
    : ∀{P k r}{rc : RecordChain r}(c : 𝕂-chain P k rc) → RecordChain r
  kchainForget {rc = rc} _ = rc

  kchain-to-RecordChain-at-b⟦⟧
    : ∀{P k r}{rc : RecordChain r}(c : 𝕂-chain P k rc)(ix : Fin k)
    → RecordChain (B (c b⟦ ix ⟧))
  kchain-to-RecordChain-at-b⟦⟧ 0-chain ()
  kchain-to-RecordChain-at-b⟦⟧ (s-chain {rc = rc} r←b {pb} x b←q {pq} c) zero
    = (step rc r←b {pb})
  kchain-to-RecordChain-at-b⟦⟧ (s-chain r←b x b←q c) (suc zz)
    = kchain-to-RecordChain-at-b⟦⟧ c zz

  kchainBlockRoundZero-lemma
    : ∀{k q P}{rc : RecordChain (Q q)}(c : 𝕂-chain P (suc k) rc)
    → getRound (kchainBlock zero c) ≡ getRound q
  kchainBlockRoundZero-lemma (s-chain r←b prf (B←Q r h) c) = sym r

  kchainBlockRound≤ : ∀{k r P}{rc : RecordChain r}(x y : Fin k)(kc : 𝕂-chain P k rc)
                    → x ≤Fin y → getRound (kchainBlock y kc) ≤ getRound (kchainBlock x kc)
  kchainBlockRound≤ zero zero (s-chain r←b prf b←q kc) hyp = ≤-refl
  kchainBlockRound≤ zero (suc y) (s-chain (Q←B r r←b) prf b←q (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc)) hyp 
    = ≤-trans (kchainBlockRound≤ zero y (s-chain r←b₁ prf₁ (B←Q refl b←q₁) kc) z≤n) (<⇒≤ r)
  kchainBlockRound≤ (suc x) (suc y) (s-chain r←b prf b←q kc) (s≤s hyp) 
    = kchainBlockRound≤ x y kc hyp

  Contig : Record → Record → Set
  Contig r r' = round r' ≡ suc (round r)

  kchain-round-≤-lemma'
    : ∀{k q}{rc : RecordChain (Q q)}(c3 : 𝕂-chain Contig k rc)(ix : Fin k)
    → getRound (c3 b⟦ ix ⟧) ≤ getRound q
  kchain-round-≤-lemma' (s-chain r←b x (B←Q refl b←q) c3) zero = ≤-refl
  kchain-round-≤-lemma' (s-chain (I←B prf imp) refl (B←Q refl _) 0-chain) (suc ()) 
  kchain-round-≤-lemma' (s-chain (Q←B prf imp) x (B←Q refl _) c2) (suc ix) 
    = ≤-trans (kchain-round-≤-lemma' c2 ix) (≤-unstep prf)

  Simple : Record → Record → Set
  Simple _ _ = Unit

  𝕂-chain-contig : (k : ℕ){r : Record} → RecordChain r → Set
  𝕂-chain-contig = 𝕂-chain Contig

  -- States that a given record belongs in a record chain.
  data _∈RC_ (r₀ : Record) : ∀{r₁} → RecordChain r₁ → Set where
    here   : ∀{rc : RecordChain r₀} → r₀ ∈RC rc
    there  : ∀{r₁ r₂}{rc : RecordChain r₁}(p : r₁ ← r₂)
           → r₀ ∈RC rc
           → {prf : IsInPool r₂}
           → r₀ ∈RC (step rc p {prf})

  kchainBlock-correct
    : ∀{P k q b}{rc : RecordChain (B b)}{b←q : B b ← Q q}{ipq : IsInPool (Q q)}
    → (kc : 𝕂-chain P k (step rc b←q {ipq}))
    → (x : Fin k) → (B (kc b⟦ x ⟧)) ∈RC rc
  kchainBlock-correct (s-chain r←b prf b←q kc) zero = here
  kchainBlock-correct (s-chain r←b prf b←q (s-chain r←b₁ prf₁ b←q₁ kc)) (suc x) 
    = there r←b (there b←q₁ (kchainBlock-correct (s-chain r←b₁ prf₁ b←q₁ kc) x))

  𝕂-chain-∈RC : ∀{r k P}{rc : RecordChain r}
              → (c : 𝕂-chain P k rc)
              → (x y : Fin k)
              → x ≤Fin y
              → {b : Block}(prf : kchainBlock x c ≡ b)
              → (rc₁ : RecordChain (B b))
              → HashBroke ⊎ (B (kchainBlock y c) ∈RC rc₁)
  𝕂-chain-∈RC (s-chain r←b {inP} prf b←q c) zero y z≤n refl rc1 
    with RecordChain-irrelevant (step (kchainForget c) r←b {inP}) rc1
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl = inj₂ (kchainBlock-correct (s-chain r←b {inP} prf b←q c) y)
  𝕂-chain-∈RC (s-chain r←b prf b←q c) (suc x) (suc y) (s≤s x≤y) hyp rc1 
   = 𝕂-chain-∈RC c x y x≤y hyp rc1

  ------------------------
  -- Lemma 1

  InitialIrrel : (i j : Initial) → i ≡ j
  InitialIrrel mkInitial mkInitial = refl

  -- LemmaS1-1 states that a record that has been flagged as 'valid' (paper section 4.2)
  -- depends upon the initial record.
  lemmaS1-1 : {r : Record}
            → RecordChain r
            → (I mkInitial) ←⋆ r
  lemmaS1-1 empty = ssRefl
  lemmaS1-1 {r} (step rc ext) = ssStep (lemmaS1-1 rc) ext

  -----------------
  -- Commit Rule --

  -- A block (and everything preceeding it) is said to match the commit rule
  -- when the block is the head of a contiguious 3-chain. Here we define an auxiliary
  -- datatype to make definitions more bearable.
  data CommitRule : ∀{r} → RecordChain r → Block → Set where
    commit-rule : ∀{r b}{rc : RecordChain r}(c3 : 𝕂-chain Contig 3 rc) 
                → b ≡ c3 b⟦ suc (suc zero) ⟧
                → CommitRule rc b

  vote≡⇒QPrevHash≡ : {q q' : QC} {v v' : Vote} 
                   → v  ∈ qcVotes q
                   → v' ∈ qcVotes q'
                   → v ≡ v' 
                   → getPrevHash q ≡ getPrevHash q'
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

  ¬bRound≡0 : ∀ {b} → RecordChain (B b) → ¬ (getRound b ≡ 0)
  ¬bRound≡0 (step s (I←B () h)) refl
  ¬bRound≡0 (step s (Q←B () h)) refl
