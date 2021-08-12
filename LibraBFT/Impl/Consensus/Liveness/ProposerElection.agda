{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.Liveness.ProposerElection where

postulate
  getValidProposer : ProposerElection → Round → Author

isValidProposerM : Author → Round → LBFT Bool
isValidProposer : ProposerElection → Author → Round → Bool

isValidProposalM : Block → LBFT (Either ObmNotValidProposerReason Unit)
isValidProposalM b =
  maybeSD (b ^∙ bAuthor) (bail ProposalDoesNotHaveAnAuthor) $ λ a → do
    -- IMPL-DIFF: `ifM` in Haskell means something else
    vp ← isValidProposerM a (b ^∙ bRound)
    ifD vp
      then ok unit
      else bail ProposerForBlockIsNotValidForThisRound

isValidProposerM a r = isValidProposer <$> use lProposerElection <*> pure a <*> pure r

isValidProposer pe a r = getValidProposer pe r == a
