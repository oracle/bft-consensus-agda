{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Hash

open import LibraBFT.Abstract.Types

open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Consensus.Types

open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.Obligations
import LibraBFT.Concrete.Properties.VotesOnce   as VO
import LibraBFT.Concrete.Properties.LockedRound as LR

open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms

-- In this module, we assume that the implementation meets its
-- obligations, and use this assumption to prove that the
-- implementatioon enjoys one of the per-epoch correctness conditions
-- proved in Abstract.Properties.  It can be extended to other
-- properties later.

module LibraBFT.Concrete.Properties (impl-correct : ImplObligations) where
  open ImplObligations impl-correct

  -- For any reachable state,
  module _ {e}(st : SystemState e)(r : ReachableSystemState st)(eid : Fin e) where
   open import LibraBFT.Concrete.System sps-cor
   open PerState st r
   open PerEpoch eid

   -- For any valid epoch within said state
   module _ (valid-𝓔 : ValidEpoch 𝓔) where
    import LibraBFT.Abstract.Records 𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔) as Abs
    open import LibraBFT.Abstract.RecordChain 𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)
    open import LibraBFT.Abstract.System 𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)
    open import LibraBFT.Abstract.Properties 𝓔 valid-𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)

    open import LibraBFT.Abstract.Obligations.VotesOnce 𝓔 valid-𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)
    open import LibraBFT.Abstract.Obligations.LockedRound 𝓔 valid-𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)

    validState : ValidSysState ConcSystemState
    validState = record
      { vss-votes-once   = VO.Proof.voo sps-cor vo₁ vo₂ st r eid valid-𝓔
      ; vss-locked-round = LR.Proof.lrr sps-cor lr₁ st r eid valid-𝓔
      }

    open All-InSys-props (AbsSystemState.InSys ConcSystemState)

    -- commited blocks do not conflict.
    S5 : ∀{q q'}
       → {rc  : RecordChain (Abs.Q q)}  → All-InSys rc
       → {rc' : RecordChain (Abs.Q q')} → All-InSys rc'
       → {b b' : Abs.Block}
       → CommitRule rc  b
       → CommitRule rc' b'
       → NonInjective-≡ Abs.bId ⊎ ((Abs.B b) ∈RC rc' ⊎ (Abs.B b') ∈RC rc)
    S5 = CommitsDoNotConflict ConcSystemState validState
