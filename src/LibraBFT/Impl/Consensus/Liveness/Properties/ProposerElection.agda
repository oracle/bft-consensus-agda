{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.Liveness.ProposerElection
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.LBFT
open import Optics.All
open import Util.Lemmas
open import Util.Prelude
open import Util.Types

module LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection where

-- TUTORIAL
module isValidProposalMSpec (b : Block) where

  pe      = _^∙ lProposerElection
  mAuthor = b ^∙ bAuthor
  round   = b ^∙ bRound

  contract
    : ∀ pre Post
      → (mAuthor ≡ nothing → Post (Left ProposalDoesNotHaveAnAuthor) pre [])
      → (Maybe-Any (getValidProposer (pe pre) round ≢_) mAuthor
         → Post (Left ProposerForBlockIsNotValidForThisRound) pre [])
      → (Maybe-Any (getValidProposer (pe pre) round ≡_) mAuthor
         → Post (Right unit) pre [])
      → LBFT-weakestPre (isValidProposalM b) Post pre
  -- 1. `isValidProposalM` begins with `RWS-maybe`, so we must provide two cases:
  --    one where `b ^∙ bAuthor` is `nothing` and one where it is `just`
  --    something
  -- 2. When it is nothing, we appeal to the assumed proof
  proj₁ (contract pre Post pfNone pf≢ pfOk) mAuthor≡nothing = pfNone mAuthor≡nothing
  -- 3. When it is something, we step into `isValidProposerM`. This means:
  --    - we use the proposer election of the round manager (`pe` and `pe≡`)
  --    - we apply `isValidProposer` to `pe`  (`isvp-pe` and `isvp-pe≡`)
  --    - we push the pure value `a` into the LBFT monad and apply `isvp-pe` to
  --      it (`.a`, `isvp-pe-a`, and `isvp-pe-a≡`)
  --    - we push the pure value `b ^∙ bRound` (`r` and `r≡`) into the LBFT
  --      monad, and the returned value is the result of applying `isvp-pe-a` to
  --      this
  --    - now out of `isValidProposalM`, we are given an alias `r'` for `r`
  -- > proj₂ (contract Post pre pfNone pf≢ pfOk) a ma≡just-a isvp isvp≡ pe pe≡ isvp-pe isvp-pe≡ .a refl isvp-pe-a isvp-pe-a≡ r r≡ r' r'≡ = {!!}
  -- 4. Since the returned value we want to reason about is directly related to
  --    the behavior of these bound functions which are partial applications of
  --    `isValidProposer`, we perform case-analysis on each of the equality
  --    proofs (we can't pattern match on `ma≡just-a` directly)
  -- > proj₂ (contract pre Post pfNone pf≢ pfOk) a ma≡just-a ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl = {!!}
  -- 5. Now we encounter an `ifD`, which means we must provide two cases, one corresponding to each branch.
  proj₁ (proj₂ (contract pre Post pfNone pf≢ pfOk) a ma≡just-a ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl) vp≡true
  -- 6. The types of `pfOk` and `pf≢` are still "stuck" on the expression
  -- > b ^∙ bAuthor
  --    So, in both the `false` and `true` cases we rewrite by `ma≡just-a`, which
  --    tells us that the result is `just a`
    rewrite ma≡just-a =
  -- 7. To finish, we use `toWitnessF` to convert between the two forms of evidence.
    pfOk (just (toWitnessT vp≡true))
  proj₂ (proj₂ (contract pre Post pfNone pf≢ pfOk) a ma≡just-a ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl) vp≡false
    rewrite ma≡just-a =
    pf≢ (just (toWitnessF vp≡false))
