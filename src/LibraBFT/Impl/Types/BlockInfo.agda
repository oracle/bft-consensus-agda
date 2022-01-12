{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Crypto.Crypto.Hash               as Hash
import      LibraBFT.Impl.OBM.Crypto                       as Crypto
import      LibraBFT.Impl.Types.OnChainConfig.ValidatorSet as ValidatorSet
import      LibraBFT.Impl.Types.ValidatorVerifier          as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.Prelude

module LibraBFT.Impl.Types.BlockInfo where

gENESIS_EPOCH   : Epoch
gENESIS_EPOCH   = {-Epoch-} 0

gENESIS_ROUND   : Round
gENESIS_ROUND   = {-Round-} 0

gENESIS_VERSION : Version
gENESIS_VERSION = Version∙new 0 0

empty : BlockInfo
empty = BlockInfo∙new
  gENESIS_EPOCH
  gENESIS_ROUND
  Hash.valueZero
  Hash.valueZero
  gENESIS_VERSION
  nothing

genesis : HashValue → ValidatorSet → Either ErrLog BlockInfo
genesis genesisStateRootHash validatorSet = do
  vv ← ValidatorVerifier.from-e-abs validatorSet
  pure $ BlockInfo∙new
    gENESIS_EPOCH
    gENESIS_ROUND
    Hash.valueZero
    genesisStateRootHash
    gENESIS_VERSION
  --gENESIS_TIMESTAMP_USECS
    (just (EpochState∙new {-Epoch-} 1 vv))

mockGenesis : Maybe ValidatorSet → Either ErrLog BlockInfo
mockGenesis
  = genesis
    (Crypto.obmHashVersion gENESIS_VERSION) -- OBM-LBFT-DIFF : Crypto.aCCUMULATOR_PLACEHOLDER_HASH
  ∘ fromMaybe ValidatorSet.empty

hasReconfiguration : BlockInfo → Bool
hasReconfiguration = is-just ∘ (_^∙ biNextEpochState)
