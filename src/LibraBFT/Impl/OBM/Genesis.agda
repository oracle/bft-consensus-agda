{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Types.CryptoProxies              as CryptoProxies
import      LibraBFT.Impl.Types.LedgerInfo                 as LedgerInfo
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures   as LedgerInfoWithSignatures
import      LibraBFT.Impl.Types.ValidatorSigner            as ValidatorSigner
import      LibraBFT.Impl.Types.ValidatorVerifier          as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.OBM.Genesis where

------------------------------------------------------------------------------

obmMkLedgerInfoWithEpochState : ValidatorSet → Either ErrLog LedgerInfo

------------------------------------------------------------------------------

obmMkGenesisLedgerInfoWithSignatures
  : List ValidatorSigner → ValidatorSet → Either ErrLog LedgerInfoWithSignatures
obmMkGenesisLedgerInfoWithSignatures vss0 vs0 = do
  liwes    ← obmMkLedgerInfoWithEpochState vs0
  let sigs = fmap (λ vs → (vs ^∙ vsAuthor , ValidatorSigner.sign vs liwes)) vss0
  pure $ foldl' (λ acc (a , sig) → CryptoProxies.addToLi a sig acc)
                (LedgerInfoWithSignatures.obmNewNoSigs liwes)
                sigs

obmMkLedgerInfoWithEpochState vs = do
  li ← LedgerInfo.mockGenesis (just vs)
  vv ← ValidatorVerifier.from-e-abs vs
  pure (li
         & liCommitInfo ∙ biNextEpochState
        ?~ EpochState∙new (li ^∙ liEpoch) vv)
