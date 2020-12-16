{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Properties.Aux

open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.VotesOnce as VO

open import LibraBFT.Yasm.AvailableEpochs
open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms
open        Structural impl-sps-avp

open import LibraBFT.Concrete.Obligations

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  postulate  -- TODO-3 : prove
    vo₁ : VO.ImplObligation₁
    vo₂ : VO.ImplObligation₂
