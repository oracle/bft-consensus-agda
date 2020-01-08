open import LibraBFT.Prelude
open import LibraBFT.Base.Types

module LibraBFT.Abstract.Rules (ec : EpochConfig) where

  open import LibraBFT.Abstract.BFT     ec
  open import LibraBFT.Abstract.Records ec

  ---------------------------------------
  -- Honesty and Dishonesty of Authors --

  data Dishonest (α : Author ec) : Set where

    -- MSM: DANGER!  This scenario does NOT indicate that α is dishonest.  The two votes could
    -- be the same votes, included in different QCs (possibly constructed by someone *else*
    -- dishonest).  This shows that we'd better be pretty careful with this approach, as it's an
    -- invitation to introduce contradictory postulates (via ACCOUNTABILITY-OPP).
    same-order-diff-qcs-DO-NOT-USE 
      : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
      → q ≢ q'
      → voteOrder (∈QC-Vote q vα) ≡ voteOrder (∈QC-Vote q' vα')
      → Dishonest α

  postulate
    ACCOUNTABILITY-OPP : ∀{α} → Honest α → Dishonest α → ⊥

