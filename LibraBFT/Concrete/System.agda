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
open import LibraBFT.Impl.Handle sha256 sha256-cr
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig

-- This module defines an abstract system state given a reachable
-- concrete system state.

module LibraBFT.Concrete.System where

 ℓ-VSFP : Level
 ℓ-VSFP = 1ℓ ℓ⊔ ℓ-RoundManager

 open import LibraBFT.Yasm.Base
 import      LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms as LYS
 open import LibraBFT.Abstract.Util.AvailableEpochs NodeId ℓ-EC EpochConfig epochId renaming (lookup'' to AE-lookup)

 -- What EpochConfigs are known in the system?  For now, only the initial one.  Later, we will add
 -- knowledge of subsequent EpochConfigs known via EpochChangeProofs.
 data EpochConfig∈Sys (st : LYS.SystemState) (𝓔 : EpochConfig) : Set ℓ-EC where
   inGenInfo : init-EC genInfo ≡ 𝓔 → EpochConfig∈Sys st 𝓔
   -- inECP  : ∀ {ecp} → ecp ECP∈Sys st → verify-ECP ecp 𝓔 → EpochConfig∈Sys 

 -- A peer pid can sign a new message for a given PK if pid is the owner of a PK in a known
 -- EpochConfig.  
 record PeerCanSignForPK (st : LYS.SystemState) (v : Vote) (pid : NodeId) (pk : PK) : Set ℓ-VSFP where
   constructor mkPCS4PK
   field
     𝓔       : EpochConfig
     𝓔id≡    : epochId 𝓔 ≡ v ^∙ vEpoch
     𝓔inSys  : EpochConfig∈Sys st 𝓔
     mbr      : Member 𝓔
     nid≡     : toNodeId  𝓔 mbr ≡ pid
     pk≡      : getPubKey 𝓔 mbr ≡ pk
 open PeerCanSignForPK

 PCS4PK⇒NodeId-PK-OK : ∀ {rmam v pid pk} → (pcs : PeerCanSignForPK rmam v pid pk) → NodeId-PK-OK (𝓔 pcs) pk pid
 PCS4PK⇒NodeId-PK-OK (mkPCS4PK _ _ _ mbr n≡ pk≡) = mbr , n≡ , pk≡

 noEpochChangeSPS₁ : ∀ {st pid ps' msgs}
                  → LYS.initialised st pid ≡ LYS.initd
                  → LYS.StepPeerState pid (LYS.msgPool st) (LYS.initialised st) (LYS.peerStates st pid) (ps' , msgs)
                  → ₋rmamMetaNumEpochs ps' ≡ ₋rmamMetaNumEpochs (LYS.peerStates st pid)
 noEpochChangeSPS₁ ini (LYS.step-init uni) = ⊥-elim (LYS.uninitd≢initd (trans (sym uni) ini))
 noEpochChangeSPS₁ _ (LYS.step-msg {_ , P x} m∈pool ini) = refl
 noEpochChangeSPS₁ _ (LYS.step-msg {_ , V x} m∈pool ini) = refl
 noEpochChangeSPS₁ _ (LYS.step-msg {_ , C x} m∈pool ini) = refl

 noEpochChangeSPS₂ : ∀ {st pid ps' msgs}
                   → LYS.initialised st pid ≡ LYS.initd
                   → LYS.StepPeerState pid (LYS.msgPool st) (LYS.initialised st) (LYS.peerStates st pid) (ps' , msgs)
                   → (num𝓔s≡ : ₋rmamMetaNumEpochs ps' ≡ ₋rmamMetaNumEpochs (LYS.peerStates st pid))
                   → ₋rmamMetaAvailEpochs (LYS.peerStates st pid) ≡ subst AvailableEpochs num𝓔s≡ (₋rmamMetaAvailEpochs ps')
 noEpochChangeSPS₂ ini (LYS.step-init uni) _ = ⊥-elim (LYS.uninitd≢initd (trans (sym uni) ini))
 noEpochChangeSPS₂ _  (LYS.step-msg {_ , P x} _ ini) num𝓔s≡ rewrite num𝓔s≡ = refl
 noEpochChangeSPS₂ _  (LYS.step-msg {_ , V x} _ ini) num𝓔s≡ rewrite num𝓔s≡ = refl
 noEpochChangeSPS₂ _  (LYS.step-msg {_ , C x} _ ini) num𝓔s≡ rewrite num𝓔s≡ = refl

 -- This is super simple for now because the only known EpochConfig is dervied from genInfo, which is not state-dependent
 PeerCanSignForPK-stable : LYS.ValidSenderForPK-stable-type PeerCanSignForPK
 PeerCanSignForPK-stable _ _ (mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁) = (mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁)

 open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK
                                                                  (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

 -- An implementation must prove that, if one of its handlers sends a
 -- message that contains a vote and is signed by a public key pk, then
 -- either the vote's author is the peer executing the handler, the
 -- epochId is in range, the peer is a member of the epoch, and its key
 -- in that epoch is pk; or, a message with the same signature has been
 -- sent before.  This is represented by StepPeerState-AllValidParts.
 module WithSPS (sps-corr : StepPeerState-AllValidParts) where

   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr

   -- TODO-1: refactor this somewhere else?  Maybe something like
   -- LibraBFT.Impl.Consensus.Types.Properties?
   sameHonestSig⇒sameVoteData : ∀ {v1 v2 : Vote} {pk}
                              → Meta-Honest-PK pk
                              → WithVerSig pk v1
                              → WithVerSig pk v2
                              → v1 ^∙ vSignature ≡ v2 ^∙ vSignature
                              → NonInjective-≡ sha256 ⊎ v2 ^∙ vVoteData ≡ v1 ^∙ vVoteData
   sameHonestSig⇒sameVoteData {v1} {v2} hpk wvs1 wvs2 refl
      with verify-bs-inj (verified wvs1) (verified wvs2)
        -- The signable fields of the votes must be the same (we do not model signature collisions)
   ...| bs≡
        -- Therefore the LedgerInfo is the same for the new vote as for the previous vote
        = sym <⊎$> (hashVote-inj1 {v1} {v2} (sameBS⇒sameHash bs≡))

   -- We are now ready to define an 'IntermediateSystemState' view for a concrete
   -- reachable state.  We will do so by fixing an epoch that exists in
   -- the system, which will enable us to define the abstract
   -- properties. The culminaton of this 'PerEpoch' module is seen in
   -- the 'IntSystemState' "function" at the bottom, which probably the
   -- best place to start uynderstanding this.  Longer term, we will
   -- also need higher-level, cross-epoch properties.
   module PerState (st : SystemState)(r : ReachableSystemState st) where

    -- TODO-3: Remove this postulate when we are satisfied with the
    -- "hash-collision-tracking" solution. For example, when proving voo
    -- (in LibraBFT.LibraBFT.Concrete.Properties.VotesOnce), we
    -- currently use this postulate to eliminate the possibility of two
    -- votes that have the same signature but different VoteData
    -- whenever we use sameHonestSig⇒sameVoteData.  To eliminate the
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
         vmsgEpoch     : cv ^∙ vEpoch ≡ epochId 𝓔
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

     record ∃VoteMsgInFor (outs : List NetworkMsg)(v : Abs.Vote) : Set where
       constructor mk∃VoteMsgInFor
       field
         vmFor    : ∃VoteMsgFor v
         nmInOuts : nm vmFor ∈ outs
     open ∃VoteMsgInFor public

     ∈QC⇒sent : ∀{st : SystemState} {q α}
              → Abs.Q q α-Sent (msgPool st)
              → Meta-Honest-Member α
              → (vα : α Abs.∈QC q)
              → ∃VoteMsgSentFor (msgPool st) (Abs.∈QC-Vote q vα)
     ∈QC⇒sent {e} {st} {α = α} vsent@(ws {sender} {nm} e≡ nm∈st (qc∈NM {cqc} {q} .{nm} valid cqc∈nm q≡)) ha va
       with All-reduce⁻ {vdq = Any-lookup va} (α-Vote cqc valid) All-self
                        (subst (Any-lookup va ∈_) (cong Abs.qVotes q≡) (Any-lookup-correctP va))
     ...| as , as∈cqc , α≡
       with  α-Vote-evidence cqc valid  as∈cqc | inspect
            (α-Vote-evidence cqc valid) as∈cqc
     ...| ev | [ refl ]
        with vote∈qc {vs = as} as∈cqc refl cqc∈nm
     ...| v∈nm =
          mk∃VoteMsgSentFor
                   (mk∃VoteMsgFor nm (₋cveVote ev) v∈nm
                                  (₋ivvMember (₋cveIsValidVote ev))
                                  (₋ivvSigned (₋cveIsValidVote ev)) (sym α≡)
                                  (₋ivvEpoch (₋cveIsValidVote ev)))
                   sender
                   nm∈st

     -- Finally, we can define the abstract system state corresponding to the concrete state st
     IntSystemState : IntermediateSystemState ℓ0
     IntSystemState = record
       { InSys           = λ { r → r α-Sent (msgPool st) }
       ; HasBeenSent     = λ { v → ∃VoteMsgSentFor (msgPool st) v }
       ; ∈QC⇒HasBeenSent = ∈QC⇒sent {st = st}
       }
