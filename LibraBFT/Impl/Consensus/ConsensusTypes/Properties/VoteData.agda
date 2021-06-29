{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData as VoteData
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All

open RWST-do

module LibraBFT.Impl.Consensus.ConsensusTypes.Properties.VoteData (self : VoteData) where

  record Contract : Set where
    constructor mkContract
    field
      ep≡     : self ^∙ vdParent ∙ biEpoch ≡ self ^∙ vdProposed ∙ biEpoch
      parRnd< : self ^∙ vdParent ∙ biRound < self ^∙ vdProposed ∙ biRound
      parVer≤ : (self ^∙ vdParent ∙ biVersion) ≤-Version (self ^∙ vdProposed ∙ biVersion)
  open Contract

  contract
      : VoteData.verify self ≡ Right unit → Contract
  contract
     with self ^∙ vdParent ∙ biEpoch ≟ self ^∙ vdProposed ∙ biEpoch
  ...| no neq = (λ ())
  ...| yes refl
     with self ^∙ vdParent ∙ biRound <? self ^∙ vdProposed ∙ biRound
  ...| no ¬par<prop = (λ ())
  ...| yes par<prop
     with (self ^∙ vdParent ∙ biVersion) ≤?-Version (self ^∙ vdProposed ∙ biVersion)
  ...| no ¬parVer≤ = (λ ())
  ...| yes parVer≤ = (λ x → mkContract refl par<prop parVer≤)
