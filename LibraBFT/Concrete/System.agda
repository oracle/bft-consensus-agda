{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import Optics.All

open        EpochConfig

-- This module defines an abstract system state (represented by a value of type
-- 'IntermediateSystemState') for a given concrete state.  The culminaton of this
-- module is the 'intSystemState' "function" at the bottom, which is probably the
-- best place to start understanding this.  Longer term, we will also need
-- higher-level, cross-epoch properties.

module LibraBFT.Concrete.System where

 open import LibraBFT.Yasm.Base
 open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

 module PerState (st : SystemState) where
    module PerEpoch (𝓔 : EpochConfig) where

     open import LibraBFT.Abstract.Abstract     UID _≟UID_ NodeId 𝓔 (ConcreteVoteEvidence 𝓔) as Abs hiding (qcVotes; Vote)
     open import LibraBFT.Concrete.Intermediate                   𝓔 (ConcreteVoteEvidence 𝓔)
     open import LibraBFT.Concrete.Records                        𝓔

     -- * Auxiliary definitions;
     -- Here we capture the idea that there exists a vote message that
     -- witnesses the existence of a given Abs.Vote
     record ∃VoteMsgFor (v : Abs.Vote) : Set where
       constructor mk∃VoteMsgFor
       field
         -- A message that was actually sent
         nm            : NetworkMsg
         cv            : Vote
         cv∈nm         : cv ⊂Msg nm
         -- And contained a valid vote that, once abstracted, yeilds v.
         vmsgMember    : EpochConfig.Member 𝓔
         vmsgSigned    : WithVerSig (getPubKey 𝓔 vmsgMember) cv
         vmsg≈v        : α-ValidVote 𝓔 cv vmsgMember ≡ v
         vmsgEpoch     : cv ^∙ vEpoch ≡ epoch 𝓔
     open ∃VoteMsgFor public

     record ∃VoteMsgSentFor (sm : SentMessages)(v : Abs.Vote) : Set where
       constructor mk∃VoteMsgSentFor
       field
         vmFor        : ∃VoteMsgFor v
         vmSender     : NodeId
         nmSentByAuth : (vmSender , (nm vmFor)) ∈ sm
     open ∃VoteMsgSentFor public

     ∈QC⇒sent : ∀{st : SystemState} {q α}
              → Abs.Q q α-Sent (msgPool st)
              → Meta-Honest-Member α
              → (vα : α Abs.∈QC q)
              → ∃VoteMsgSentFor (msgPool st) (Abs.∈QC-Vote q vα)
     ∈QC⇒sent vsent@(ws {sender} {nm} e≡ nm∈st (qc∈NM {cqc} {q} .{nm} valid cqc∈nm)) ha va
       with All-reduce⁻ {vdq = Any-lookup va} (α-Vote cqc valid) All-self
                        (Any-lookup-correctP va)
     ...| as , as∈cqc , α≡
       with  α-Vote-evidence cqc valid  as∈cqc | inspect
            (α-Vote-evidence cqc valid) as∈cqc
     ...| ev | [ refl ]
        with vote∈qc {vs = as} as∈cqc refl cqc∈nm
     ...| v∈nm = mk∃VoteMsgSentFor
                   (mk∃VoteMsgFor nm (_cveVote ev) v∈nm
                                  (_ivvMember (_cveIsValidVote ev))
                                  (_ivvSigned (_cveIsValidVote ev)) (sym α≡)
                                  (_ivvEpoch  (_cveIsValidVote ev)))
                   sender
                   nm∈st

     -- Finally, we can define the abstract system state corresponding to the concrete state st
     intSystemState : IntermediateSystemState ℓ0
     intSystemState = record
       { InSys           = λ { r → r α-Sent (msgPool st) }
       ; HasBeenSent     = λ { v → ∃VoteMsgSentFor (msgPool st) v }
       ; ∈QC⇒HasBeenSent = ∈QC⇒sent {st = st}
       }
