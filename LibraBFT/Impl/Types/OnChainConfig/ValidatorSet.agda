{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                 as Map hiding (empty)
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.OnChainConfig.ValidatorSet where

new : List ValidatorInfo → ValidatorSet
new = ValidatorSet∙new ConsensusScheme∙new

empty : ValidatorSet
empty = new []

obmFromVV : ValidatorVerifier → ValidatorSet
obmFromVV vv0 = record -- ValidatorSet
  { _vsScheme  = ConsensusScheme∙new -- TODO
  ; _vsPayload = fmap go (Map.toList (vv0 ^∙ vvAddressToValidatorInfo))
  }
 where
  go : (Author × ValidatorConsensusInfo) → ValidatorInfo
  go (address , ValidatorConsensusInfo∙new pk vp) =
    record -- ValidatorInfo
    { _viAccountAddress = address
    ; _viConsensusVotingPower = vp
    ; _viConfig = record -- ValidatorConfig
                  { _vcConsensusPublicKey      = pk
                  ; _vcValidatorNetworkAddress = address ^∙ aAuthorName } }

obmGetValidatorInfo : AuthorName → ValidatorSet → Either ErrLog ValidatorInfo
obmGetValidatorInfo name vs = go (vs ^∙ vsPayload)
 where
  go : List ValidatorInfo → Either ErrLog ValidatorInfo
  go        []  = Left fakeErr -- ["ValidatorSet", "obmGetValidatorInfo", "TODO better err msg"]
  go (vi ∷ vis) = if-dec vi ^∙ viAccountAddress ∙ aAuthorName ≟ name then pure vi else go vis
