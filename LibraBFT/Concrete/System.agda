{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig

-- This module defines an abstract system state (represented by a value
-- of type 'IntermediateSystemState') for a given concrete reachable
-- state.  The culminaton of this proof is seen in the 'intSystemState'
-- "function" at the bottom, which is probably the best place to start
-- understanding this.  Longer term, we will also need higher-level,
-- cross-epoch properties.

module LibraBFT.Concrete.System where

 open import LibraBFT.Yasm.Base
 import      LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms as LYS


 open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK
                                                                  (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

 module PerState (st : SystemState)(r : ReachableSystemState st) where

    -- TODO-3: Remove this postulate when we are satisfied with the
    -- "hash-collision-tracking" solution. For example, when proving voo
    -- (in LibraBFT.LibraBFT.Concrete.Properties.VotesOnce), we
    -- currently use this postulate to eliminate the possibility of two
    -- votes that have the same signature but different VoteData
    -- whenever we use sameSig⇒sameVoteData.  To eliminate the
    -- postulate, we need to refine the properties we prove to enable
    -- the possibility of a hash collision, in which case the required
    -- property might not hold.  However, it is not sufficient to simply
    -- prove that a hash collision *exists* (which is obvious,
    -- regardless of the LibraBFT implementation).  Rather, we
    -- ultimately need to produce a specific hash collision and relate
    -- it to the data in the system, so that we can prove that the
    -- desired properties hold *unless* an actual hash collision is
    -- found by the implementation given the data in the system.  In
    -- the meantime, we simply require that the collision identifies a
    -- reachable state; later "collision tracking" will require proof
    -- that the colliding values actually exist in that state.
    postulate  -- temporary assumption that hash collisions don't exist (see comment above)
      meta-sha256-cr : ¬ (NonInjective-≡ sha256)

    sameSig⇒sameVoteDataNoCol : ∀ {v1 v2 : Vote} {pk}
                              → WithVerSig pk v1
                              → WithVerSig pk v2
                              → v1 ^∙ vSignature ≡ v2 ^∙ vSignature
                              → v2 ^∙ vVoteData ≡ v1 ^∙ vVoteData
    sameSig⇒sameVoteDataNoCol {v1} {v2} wvs1 wvs2 refl
       with sameSig⇒sameVoteData {v1} {v2} wvs1 wvs2 refl
    ...| inj₁ hb = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ x = x

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
         -- And contained a valid vote that, once abstracted, yields v.
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

     ∃VoteMsgSentFor-stable : ∀ {pre : SystemState} {post : SystemState} {v}
                            → Step pre post
                            → ∃VoteMsgSentFor (msgPool pre) v
                            → ∃VoteMsgSentFor (msgPool post) v
     ∃VoteMsgSentFor-stable theStep (mk∃VoteMsgSentFor sndr vmFor sba) =
                                     mk∃VoteMsgSentFor sndr vmFor (msgs-stable theStep sba)

     open WithAbsVote

     MWSS⇒∃VMS : ∀ {vabs v pool}
               → v ^∙ vEpoch ≡ epoch 𝓔
               → (wvs : WithVerSig (getPubKey 𝓔 (abs-vMember vabs)) v)
               → MsgWithSig∈ (getPubKey 𝓔 (abs-vMember vabs)) (ver-signature wvs) pool
               → α-ValidVote 𝓔 v (abs-vMember vabs) ≡ vabs
               → NonInjective-≡ sha256 ⊎
                 Σ (∃VoteMsgSentFor pool vabs) λ ∃vms → (abs-vMember vabs) ≡ vmsgMember (vmFor ∃vms)
     MWSS⇒∃VMS {vabs} refl wvs mws refl
        with sameSig⇒sameVoteData (msgSigned mws) wvs (msgSameSig mws)
     ...| inj₁ hb = inj₁ hb
     ...| inj₂ refl
        = inj₂ (mk∃VoteMsgSentFor (mk∃VoteMsgFor (msgWhole mws) (msgPart mws) (msg⊆ mws) (abs-vMember vabs)
                                                 (msgSigned mws) refl refl) (msgSender mws) (msg∈pool mws)
               , refl)


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
                   (mk∃VoteMsgFor nm (₋cveVote ev) v∈nm
                                  (₋ivvMember (₋cveIsValidVote ev))
                                  (₋ivvSigned (₋cveIsValidVote ev)) (sym α≡)
                                  (₋ivvEpoch (₋cveIsValidVote ev)))
                   sender
                   nm∈st

     -- Finally, we can define the abstract system state corresponding to the concrete state st
     intSystemState : IntermediateSystemState ℓ0
     intSystemState = record
       { InSys           = λ { r → r α-Sent (msgPool st) }
       ; HasBeenSent     = λ { v → ∃VoteMsgSentFor (msgPool st) v }
       ; ∈QC⇒HasBeenSent = ∈QC⇒sent {st = st}
       }
