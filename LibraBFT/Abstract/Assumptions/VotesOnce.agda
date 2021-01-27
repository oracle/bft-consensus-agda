open import LibraBFT.Prelude
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.Assumptions.VotesOnce
  (𝓔 : EpochConfig)(𝓔-valid : ValidEpoch 𝓔)
  (UID    : Set)
  (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
  (𝓥      : VoteEvidence 𝓔 UID)
  where

 open import LibraBFT.Abstract.Records 𝓔 UID _≟UID_ 𝓥
 import LibraBFT.Abstract.RecordChain.Invariants 𝓔 𝓔-valid UID _≟UID_ 𝓥
   as StaticInv
 open import LibraBFT.Abstract.System 𝓔 UID _≟UID_ 𝓥

 -------------------
 -- * VotesOnce * --
 -------------------

 module _ {ℓ}(𝓢 : AbsSystemState ℓ) where
  open AbsSystemState 𝓢

  Type : Set ℓ
  Type = ∀{α v v'}
       → Meta-Honest-Member 𝓔 α
       → vMember v  ≡ α → HasBeenSent v
       → vMember v' ≡ α → HasBeenSent v'
       → vRound v ≡ vRound v'
       → vBlockUID v ≡ vBlockUID v'
       -- NOTE: It is interesting that this does not require the timeout signature (or even
       -- presence/lack thereof) to be the same.  The abstract proof goes through without out it, so I
       -- am leaving it out for now, but I'm curious what if anything could go wrong if an honest
       -- author can send different votes for the same epoch and round that differ on timeout
       -- signature.  Maybe something for liveness?

  proof : Type → StaticInv.VotesOnlyOnceRule InSys
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

