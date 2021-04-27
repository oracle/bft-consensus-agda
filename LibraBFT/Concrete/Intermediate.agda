{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
-- This module defines an intermediate (between an implementation and Abstract) notion
-- of a system state.  The goal is to enable proving for a particular implementation
-- the properties required to provide to Abstract.Properties in order to get the high
-- level correctness conditions, while moving the obligations for the implementation
-- closer to notions more directly provable for an implementation.  However, as our
-- experience has developed with this, it seems that this was not a very effective
-- choice, as it leaves too much burden on the implementation (e.g., proving
-- ∈QC⇒HasBeenSent). Therefore, ...
--
-- TODO-3: Revisit assumptions of the IntermediateSystemState to enable more proof work
-- to be done under Concrete, which can be used by multiple implementations.  As it
-- currently stands, we have specific notions under LibraBFT.Impl that possibly should
-- be provided as module parameters to LibraBFT.Concrete (including IsValidVote and
-- α-ValidVote)

open import LibraBFT.Prelude
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open WithAbsVote

module LibraBFT.Concrete.Intermediate
    (𝓔 : EpochConfig)
    (𝓥 : VoteEvidence 𝓔)
   where
   open import LibraBFT.Abstract.Abstract UID _≟UID_ NodeId 𝓔 𝓥

   -- Since the invariants we want to specify (votes-once and preferred-round-rule),
   -- are predicates over a /System State/, we must factor out the necessary
   -- functionality.
   --
   -- An /IntermediateSystemState/ supports a few different notions; namely,
   record IntermediateSystemState (ℓ : Level) : Set (ℓ+1 ℓ) where
     field
       -- A notion of membership of records
       InSys : Record → Set ℓ

       -- A predicate about whether votes have been transfered
       -- amongst participants
       HasBeenSent : Vote → Set ℓ

       -- Such that, the votes that belong to honest participants inside a
       -- QC that exists in the system must have been sent
       ∈QC⇒HasBeenSent : ∀{q α} → InSys (Q q) → Meta-Honest-Member α
                       → (va : α ∈QC q) → HasBeenSent (∈QC-Vote q va)
