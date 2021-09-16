{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.Obligations
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.Prelude

open        EpochConfig
open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

-- In this module, we assume that the implementation meets its
-- obligations, and use this assumption to prove that, in any reachable
-- state, the implementatioon enjoys one of the per-epoch correctness
-- conditions proved in Abstract.Properties.  It can be extended to other
-- properties later.
module LibraBFT.Concrete.Properties
         (iiah         : SystemInitAndHandlers ℓ-RoundManager ConcSysParms)
         (st           : SystemState)
         (r            : WithInitAndHandlers.ReachableSystemState iiah st)
         (𝓔           : EpochConfig)
         (impl-correct : ImplObligations iiah 𝓔)
         where

    open WithEC
    open import LibraBFT.Abstract.Abstract     UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔) as Abs
    open import LibraBFT.Concrete.Intermediate                   𝓔 (ConcreteVoteEvidence 𝓔)
    import      LibraBFT.Concrete.Obligations.VotesOnce          𝓔 (ConcreteVoteEvidence 𝓔) as VO-obl
    import      LibraBFT.Concrete.Obligations.PreferredRound     𝓔 (ConcreteVoteEvidence 𝓔) as PR-obl
    open import LibraBFT.Concrete.Properties.VotesOnce                                       as VO
    open import LibraBFT.Concrete.Properties.PreferredRound                                  as PR
    open import LibraBFT.ImplShared.Util.HashCollisions iiah

    open        ImplObligations impl-correct
    open        PerState st
    open        PerReachableState r
    open        PerEpoch 𝓔

    --------------------------------------------------------------------------------------------
    -- * A /ValidSysState/ is one in which both peer obligations are obeyed by honest peers * --
    --------------------------------------------------------------------------------------------

    record ValidSysState {ℓ}(𝓢 : IntermediateSystemState ℓ) : Set (ℓ+1 ℓ0 ℓ⊔ ℓ) where
      field
        vss-votes-once      : VO-obl.Type 𝓢
        vss-preferred-round : PR-obl.Type 𝓢
    open ValidSysState public

    validState : ValidSysState intSystemState
    validState = record
      { vss-votes-once      = VO.Proof.voo iiah 𝓔 sps-cor gvc gvr v≢0 ∈GI? iro vo₂ st r
      ; vss-preferred-round = PR.Proof.prr iiah 𝓔 sps-cor gvr v≢0 ∈GI? iro pr₁ pr₂ st r
      }

    open IntermediateSystemState intSystemState

    open All-InSys-props InSys
    open WithAssumptions InSys

    -- We can now invoke the various abstract correctness properties.  Note that the arguments are
    -- expressed in Abstract terms (RecordChain, CommitRule).  Proving the corresponding properties
    -- for the actual implementation will involve proving that the implementation decides to commit
    -- only if it has evidence of the required RecordChains and CommitRules such that the records in
    -- the RecordChains are all "InSys" according to the implementation's notion thereof (defined in
    -- Concrete.System.intSystemState).
    ConcCommitsDoNotConflict :
       ∀{q q'}
       → {rc  : RecordChain (Abs.Q q)}  → All-InSys rc
       → {rc' : RecordChain (Abs.Q q')} → All-InSys rc'
       → {b b' : Abs.Block}
       → CommitRule rc  b
       → CommitRule rc' b'
       → NonInjective-≡-preds _ _ Abs.bId ⊎ ((Abs.B b) ∈RC rc' ⊎ (Abs.B b') ∈RC rc)
    ConcCommitsDoNotConflict = CommitsDoNotConflict
           (VO-obl.proof intSystemState (vss-votes-once validState))
           (PR-obl.proof intSystemState (vss-preferred-round validState))

    module _ (∈QC⇒AllSent : Complete InSys) where

      ConcCommitsDoNotConflict' :
        ∀{q q'}{rc  : RecordChain (Abs.Q q)}{rc' : RecordChain (Abs.Q q')}{b b' : Abs.Block}
        → InSys (Abs.Q q) → InSys (Abs.Q q')
        → CommitRule rc  b
        → CommitRule rc' b'
        → NonInjective-≡-preds _ _ Abs.bId ⊎ ((Abs.B b) ∈RC rc' ⊎ (Abs.B b') ∈RC rc)
      ConcCommitsDoNotConflict' = CommitsDoNotConflict'
           (VO-obl.proof intSystemState (vss-votes-once validState))
           (PR-obl.proof intSystemState (vss-preferred-round validState))
           ∈QC⇒AllSent

      ConcCommitsDoNotConflict''
        : ∀{o o' q q'}
        → {rcf  : RecordChainFrom o  (Abs.Q q)}
        → {rcf' : RecordChainFrom o' (Abs.Q q')}
        → {b b' : Abs.Block}
        → InSys (Abs.Q q)
        → InSys (Abs.Q q')
        → CommitRuleFrom rcf  b
        → CommitRuleFrom rcf' b'
        → NonInjective-≡ Abs.bId ⊎ Σ (RecordChain (Abs.Q q')) ((Abs.B b)  ∈RC_)
                                 ⊎ Σ (RecordChain (Abs.Q q))  ((Abs.B b') ∈RC_)
      ConcCommitsDoNotConflict'' = CommitsDoNotConflict''
           (VO-obl.proof intSystemState (vss-votes-once validState))
           (PR-obl.proof intSystemState (vss-preferred-round validState))
           ∈QC⇒AllSent

