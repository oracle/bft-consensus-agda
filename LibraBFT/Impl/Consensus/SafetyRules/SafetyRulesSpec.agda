{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRulesSpec where

module _ (e : Epoch) (sr : SafetyData) (rm : RoundManager) where
  postulate
    verifyEpochM-RW
      : let rm' = LBFT-post (verifyEpochM e sr) rm in
        rm' ≡ rm

    verifyEpochM-noOutput
      : let outs = LBFT-outs (verifyEpochM e sr) rm in
        outs ≡ []

module _ (m : MaybeSignedVoteProposal) (rm : RoundManager) where
  postulate
    constructAndSignVoteM-noOutput
      : let outs = LBFT-outs (constructAndSignVoteM m) rm
        in outs ≡ []

    constructAndSignVoteM-voteSrcCorrect
      : let result   = LBFT-result (constructAndSignVoteM m) rm
            mLastVote = rm ^∙ lPersistentSafetyStorage ∙ pssSafetyData ∙ sdLastVote
        in case result of λ where
             (inj₁ _) → Unit
             (inj₂ v) →
               v ^∙ mvSrc ≡ mvsLastVote → just (unmetaVote v) ≡ mLastVote
