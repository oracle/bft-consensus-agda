{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Liveness.ProposerElection
open import LibraBFT.Lemmas
open import LibraBFT.Prelude

module LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection where

module IsValidProposalM (b : Block) where
  -- TODO-1: This will require performing case analysis using `with` on
  -- > getValidProposer pe (b ^∙ bRound) ≟ℕ a
  -- in the case that `just a ≡ b ^∙ bAuthor`.

  open RWST-do
  contract
    : ∀ Post pre
      → let pe = pre ^∙ lProposerElection
            ma = b ^∙ bAuthor
            r  = b ^∙ bRound in
        (ma ≡ nothing ⊎ Maybe-Any (getValidProposer pe r ≢_) ma → Post false pre [])
        → (Maybe-Any (getValidProposer pe r ≡_) ma → Post true pre [])
        → RWST-weakestPre (isValidProposalM b) Post unit pre


  ≡-dec⇒true  : ∀ {m n : ℕ} → (myDec : Dec (m ≡ n)) → m ≡ n → isYes myDec ≡ true
  ≢-dec⇒false : ∀ {m n : ℕ} → (myDec : Dec (m ≡ n)) → m ≢ n → isYes myDec ≡ false

  ≡-dec⇒true  (yes refl) _   = refl
  ≡-dec⇒true  (no  neq') neq = ⊥-elim (neq' neq)
  ≢-dec⇒false (yes refl) neq = ⊥-elim (neq refl)
  ≢-dec⇒false (no  _   ) _   = refl

  -- isValidProposalM is a caseMM, so by definition of RWST-weakestPre (RWST-maybe ...), we need two
  -- properties; the first is:
  --   b ^∙ bAuthor ≡ nothing → RWST-weakestPre (RWST-return false) Post unit pre
  -- = b ^∙ bAuthor ≡ nothing → P false pre []
  -- We can get this from the provided property for the false case:
  proj₁ (contract Post pre prfF _) = prfF ∘ inj₁
  -- The second property we need is:
  -- (∀ j → b ^∙ bAuthor ≡ just j → RWST-weakestPre (isValidProposerM j (b ^∙ bRound)) Post unit pre)
  proj₂ (contract Post pre prfF prfT) = λ where a ma≡justa → aux ma≡justa
     where
       aux : ∀ {a} → b ^∙ bAuthor ≡ just a → RWST-weakestPre (isValidProposerM a (b ^∙ bRound)) Post unit pre
       aux {a} ma≡justa pe refl
          with b ^∙ bBlockData ∙ bdBlockType
       ...| NilBlock = ⊥-elim (maybe-⊥ ma≡justa refl)
       ...| Genesis  = ⊥-elim (maybe-⊥ ma≡justa refl)
       ...| Proposal _ auth rewrite just-injective ma≡justa
          with getValidProposer pe (b ^∙ bRound) ≟ℕ a
       ...| no neq =
              λ where ivppeFn refl proposer refl ivppea refl bRnd refl →
                       subst (λ b → Post b pre [])
                             (sym (≢-dec⇒false (getValidProposer pe (b ^∙ bRound) ≟ℕ a) neq))
                             (prfF (inj₂ (Maybe-Any.just neq)))
       ...| yes isProposer =
              λ where ivppeFn refl proposer refl ivppea refl bRnd refl →
                       subst (λ b → Post b pre [])
                             (sym (≡-dec⇒true (getValidProposer pe (b ^∙ bRound) ≟ℕ a) isProposer))
                             (prfT (Maybe-Any.just isProposer))
