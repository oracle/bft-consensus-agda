open import LibraBFT.Prelude
open import LibraBFT.Base.Types

module LibraBFT.Abstract.Rules (ec : EpochConfig) where

  open import LibraBFT.Abstract.BFT     ec
  open import LibraBFT.Abstract.Records ec

  ---------------------------------------
  -- Honesty and Dishonesty of Authors --

  data Dishonest (α : Author ec) : Set where
    same-order-diff-qcs 
      : {q q' : QC}(vα : α ∈QC q)(vα' : α ∈QC q')
      → q ≢ q'
      → voteOrder (∈QC-Vote q vα) ≡ voteOrder (∈QC-Vote q' vα')
      → Dishonest α

  postulate
    ACCOUNTABILITY-OPP : ∀{α} → Honest α → Dishonest α → ⊥

