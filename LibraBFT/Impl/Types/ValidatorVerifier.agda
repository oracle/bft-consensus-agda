{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Types.LedgerInfoWithSignatures as LedgerInfoWithSignatures
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.ValidatorVerifier where

getVotingPower : ValidatorVerifier → AccountAddress → Maybe U64

checkVotingPower : ValidatorVerifier → List AccountAddress → VerifyError ⊎ Unit
checkVotingPower self authors = loop authors 0
 where
  loop : List AccountAddress  → U64 → VerifyError ⊎ Unit
  loop (a ∷ as) acc = case getVotingPower self a of λ where
                        nothing  → inj₁ (UnknownAuthor (a ^∙ aAuthorName))
                        (just n) → loop as (n + acc)
  loop [] aggregatedVotingPower =
    if ⌊ aggregatedVotingPower <? self ^∙ vvQuorumVotingPower ⌋
    then (inj₁ (TooLittleVotingPower aggregatedVotingPower (self ^∙ vvQuorumVotingPower)))
    else (inj₂ unit)

getVotingPower self author =
--  (λ a → a ^∙ vciVotingPower) <$> (Map.lookup author (self ^∙ vvAddressToValidatorInfo))
  case Map.lookup author (self ^∙ vvAddressToValidatorInfo) of λ where
    nothing  → nothing
    (just a) → just (a ^∙ vciVotingPower)

