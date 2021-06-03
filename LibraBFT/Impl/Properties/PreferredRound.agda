{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
import      LibraBFT.Concrete.Properties.PreferredRound as PR

open import LibraBFT.Concrete.Obligations

-- In this module, we (will) prove the implementation obligation for the PreferredRound rule.

module LibraBFT.Impl.Properties.PreferredRound (𝓔 : EpochConfig) where

  postulate  -- TODO-3 : prove.  Note that this is a substantial
             -- undertaking that should not be started before we have
             -- a proof for the similar-but-much-simpler VotesOnce
             -- property, and also not before we have an
             -- implementation (perhaps some incremental extension of
             -- our current fake/simple implementaion) that we can
             -- reasonably hope actually ensures the property!
    pr₁ : PR.ImplObligation₁ 𝓔
    pr₂ : PR.ImplObligation₂ 𝓔
