{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types
open import Util.Prelude
open import Util.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open WithAbsVote

module LibraBFT.Concrete.Obligations.VotesOnce
  (𝓔 : EpochConfig)
  (𝓥 : VoteEvidence 𝓔)
 where
 open import LibraBFT.Abstract.Abstract      UID _≟UID_ NodeId 𝓔 𝓥
 open import LibraBFT.Concrete.Intermediate                    𝓔 𝓥

 -------------------
 -- * VotesOnce * --
 -------------------

 module _ {ℓ}(𝓢 : IntermediateSystemState ℓ) where
  open IntermediateSystemState 𝓢
  Type : Set ℓ
  Type = ∀{α v v'}
       → Meta-Honest-Member α
       → vMember v  ≡ α → HasBeenSent v
       → vMember v' ≡ α → HasBeenSent v'
       → vRound v ≡ vRound v'
       → vBlockUID v ≡ vBlockUID v'
       -- NOTE: It is interesting that this does not require the timeout signature (or even
       -- presence/lack thereof) to be the same.  The abstract proof goes through without out it, so I
       -- am leaving it out for now, but I'm curious what if anything could go wrong if an honest
       -- author can send different votes for the same epoch and round that differ on timeout
       -- signature.  Maybe something for liveness?

  proof : Type → VotesOnlyOnceRule InSys
  proof glob-inv α hα {q} {q'} q∈sys q'∈sys va va' VO≡
     with ∈QC⇒HasBeenSent q∈sys  hα va
        | ∈QC⇒HasBeenSent q'∈sys hα va'
  ...| sent-cv | sent-cv'
     with glob-inv hα (sym (∈QC-Member q  va))  sent-cv
                      (sym (∈QC-Member q' va')) sent-cv'
                      VO≡
  ...| bId≡
     = Vote-η VO≡ (trans (sym (∈QC-Member q va)) (∈QC-Member q' va'))
                  bId≡

