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

-- TUTORIAL
module isValidProposalMSpec (b : Block) where
  contract
    : ∀ Post pre
      → let pe = pre ^∙ lProposerElection
            ma = b ^∙ bAuthor
            r  = b ^∙ bRound in
        (ma ≡ nothing ⊎ Maybe-Any (getValidProposer pe r ≢_) ma → Post false pre [])
        → (Maybe-Any (getValidProposer pe r ≡_) ma → Post true pre [])
        → RWST-weakestPre (isValidProposalM b) Post unit pre
  -- 1. `isValidProposalM` begins with `caseMM`, so we must provide two cases:
  --    one where `b ^∙ bAuthor` is `nothing` and one where it is `just`
  --    something
  -- 2. When it is nothing, we appeal to the assumed proof for the false case
  proj₁ (contract Post pre prfF prfT) ma≡nothing = prfF (inj₁ ma≡nothing)
  -- 3. When it is something, we step into `isValidProposerM`. This means:
  --    - we use the proposer election of the round manager (`pe` and `pe≡`)
  --    - we apply `isValidProposer` to `pe`  (`isvp-pe` and `isvp-pe≡`)
  --    - we push the pure value `a` into the LBFT monad and apply `isvp-pe` to
  --      it (`.a`, `isvp-pe-a`, and `isvp-pe-a≡`)
  --    - we push the pure value `b ^∙ bRound` (`r` and `r≡`) into the LBFT
  --      monad, and the returned value is the result of applying `isvp-pe-a` to
  --      this
  -- > proj₂ (contract Post pre prfF prfT) a ma≡just-a isvp isvp≡ pe pe≡ isvp-pe isvp-pe≡ .a refl isvp-pe-a isvp-pe-a≡ r r≡ = {!!}
  -- 4. Since the returned value we want to reason about is directly related to
  --    the behavior of these bound functions which are partial applications of
  --    `isValidProposer`, we perform case-analysis on each of the equality
  --    proofs (we can't pattern match on `ma≡just-a` directly)
  proj₂ (contract Post pre prfF prfT) a ma≡just-a ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl
  -- 5. To proceed, abstract over the expression that is blocking case analysis
  --    on `ma≡just-a`, and inspect it for later. That way, when we analyze the
  --    boolean expression, we can remember that it came from testing whether
  --    `a` is the valid proposer for the round.
     with isValidProposer (pre ^∙ lProposerElection) a (b ^∙ bRound)
     |    inspect (isValidProposer (pre ^∙ lProposerElection) a ) (b ^∙ bRound)
  -- 6. The types of `prfT` and `prfF` are still "stuck" on the expression
  -- > b ^∙ bAuthor
  --   in both the `false` and `true` cases we rewrite by `ma≡just-a`, which
  --   tells us that the result is `just a`
  ...| false | [ vp≡ ]
    rewrite ma≡just-a =
  -- 7. `prfF ∘ Right ∘ just` wants evidence that
  -- > getValidProposer (pre ^∙ lProposerElection) (b ^∙ bRound) ≡ a
  --    but `vp≡` tells us that
  -- > ⌊ getValidProposer (pre ^∙ lProposerElection) (b ^∙ bRound) ≟ℕ a ⌋ ≡ true
  --    To finish, we use `toWitnessF` to convert between the two forms of evidence.
    prfF (Right (just (toWitnessF vp≡)))
  -- 8. A similar situation holds for the `true` case and `prfT`
  ...| true  | [ vp≡ ] rewrite ma≡just-a = prfT (just (toWitnessT vp≡))
