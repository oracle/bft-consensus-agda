{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.Common    as Common
import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.ImplFake.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState.

module LibraBFT.Impl.Properties.VotesOnce (𝓔 : EpochConfig) where

----- Properties that relate handler to system state -----

data _∈RoundManager_ (qc : QuorumCert) (rm : RoundManager) : Set where
  inHQC : qc ≡ rm ^∙ lBlockStore ∙ bsInner ∙ btHighestQuorumCert → qc ∈RoundManager rm
  inHCC : qc ≡ rm ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert → qc ∈RoundManager rm

postulate -- TODO-2: prove (waiting on: `handle`)
  -- This will be proved for the implementation, confirming that honest
  -- participants only store QCs comprising votes that have actually been sent.
  -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
  -- Note that some implementations might not ensure this, but LibraBFT does
  -- because even the leader of the next round sends its own vote to itself,
  -- as opposed to using it to construct a QC using its own unsent vote.
  qcVotesSentB4
    : ∀ {pid qc vs pk}{st : SystemState}
      → ReachableSystemState st
      → initialised st pid ≡ initd
      → qc ∈RoundManager (peerStates st pid)
      → vs ∈ qcVotes qc
      → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
      → MsgWithSig∈ pk (proj₂ vs) (msgPool st)


newVote⇒lvr≡
  : ∀ {pre : SystemState}{pid s' outs v m pk}
    → ReachableSystemState pre
    → StepPeerState pid (msgPool pre) (initialised pre)
        (peerStates pre pid) (s' , outs)
    → v ⊂Msg m → send m ∈ outs → (sig : WithVerSig pk v)
    → Meta-Honest-PK pk → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
    → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → v ^∙ vRound ≡ Meta.getLastVoteRound s'
newVote⇒lvr≡{pre}{pid}{v = v} preach (step-msg{sndr , P pm} m∈pool ini) vote∈vm m∈outs sig hpk ¬gen ¬msb4
  with handleProposalSpec.contract! 0 pm (peerStates pre pid)
... | handleProposalSpec.mkContract _ _ (Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , voteUnsent)) sdEpoch≡?) =
  ⊥-elim (unsentVoteSent voteUnsent)
  where
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  unsentVoteSent : ¬ Voting.VoteUnsentCorrect (peerStates pre pid) _ _ _ _
  unsentVoteSent (Voting.mkVoteUnsentCorrect noVoteMsgOuts _) =
    sendVote∉actions{outs = handleOuts}{st = peerStates pre pid}
      (sym noVoteMsgOuts) m∈outs
... | handleProposalSpec.mkContract _ _ (Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect (VoteMsg∙new v' _) rcvr voteMsgOuts vgCorrect)) sdEpoch≡?) =
  sentVoteIsPostLVR
  where
  handlePost = LBFT-post (handle pid (P pm) 0) (peerStates pre pid)
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  sentVoteIsPostLVR : v ^∙ vRound ≡ Meta.getLastVoteRound handlePost
  sentVoteIsPostLVR with Voting.VoteGeneratedCorrect.state vgCorrect
  ... | StateTransProps.mkVoteGenerated lv≡v _ rewrite sym lv≡v =
    cong (_^∙ vmVote ∙ vRound) (sendVote∈actions{outs = handleOuts}{st = peerStates pre pid} (sym voteMsgOuts) m∈outs)

newVote⇒lvr≡{s' = s'}{v = v} preach (step-msg{sndr , V vm} m∈pool ini) vote∈vm m∈outs sig hpk ¬gen ¬msb4 = TODO
  where
  postulate -- TODO-1: prove (note: no votes sent from processing a vote message) (waiting on: handle)
    TODO : v ^∙ vRound ≡ Meta.getLastVoteRound s'

newVote⇒lvr≡{s' = s'}{v = v} preach sps (vote∈qc vs∈qc v≈rbld qc∈m) m∈outs sig hpk ¬gen ¬msb4 = TODO
  where
  postulate -- TODO-2: prove (waiting on: proof that qc votes have been sent before)
    TODO : v ^∙ vRound ≡ Meta.getLastVoteRound s'

postulate -- TODO-3: prove
  peerCanSign-Msb4
    : ∀ {pid v pk}{pre post : SystemState}
      → ReachableSystemState pre
      → Step pre post
      → PeerCanSignForPK post v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk

  msg∈pool⇒initd
    : ∀ {pid pk v}{st : SystemState}
      → ReachableSystemState st
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → initialised st pid ≡ initd

  mws∈pool⇒epoch≡
    : ∀ {pid pk v}{st : SystemState}
      → ReachableSystemState st
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch

peerCanSignPK-Inj
  : ∀ {pid pid' pk v v'}{st : SystemState}
    → PeerCanSignForPK st v  pid  pk
    → PeerCanSignForPK st v' pid' pk
    → v ^∙ vEpoch ≡ v' ^∙ vEpoch
    → pid ≡ pid'
peerCanSignPK-Inj{pid}{pid'}{pk} pcsfpk₁ pcsfpk₂ ≡epoch = begin
  pid         ≡⟨ sym (nid≡ (pcs4in𝓔 pcsfpk₁)) ⟩
  pcsfpk₁∙pid ≡⟨ PK-inj-same-ECs{pcs4𝓔 pcsfpk₁}{pcs4𝓔 pcsfpk₂}
                   (availEpochsConsistent pcsfpk₁ pcsfpk₂ ≡epoch)
                   (begin (pcsfpk₁∙pk  ≡⟨ pk≡ (pcs4in𝓔 pcsfpk₁) ⟩
                           pk         ≡⟨ sym (pk≡ (pcs4in𝓔 pcsfpk₂)) ⟩
                           pcsfpk₂∙pk ∎)) ⟩
  pcsfpk₂∙pid ≡⟨ nid≡ (pcs4in𝓔 pcsfpk₂) ⟩
  pid'        ∎
  where
  open ≡-Reasoning
  open PeerCanSignForPKinEpoch
  open PeerCanSignForPK
  pcsfpk₁∙pid  = EpochConfig.toNodeId (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁))
  pcsfpk₁∙pk   = (EpochConfig.getPubKey (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁)))
  pcsfpk₂∙pid = EpochConfig.toNodeId (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂))
  pcsfpk₂∙pk   = (EpochConfig.getPubKey (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂)))

oldVoteRound≤lvr
  : ∀ {pid pk v}{pre : SystemState}
    → (r : ReachableSystemState pre)
    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
    → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → PeerCanSignForPK pre v pid pk
    → (peerStates pre pid) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
    → v ^∙ vRound ≤ Meta.getLastVoteRound (peerStates pre pid)
oldVoteRound≤lvr{pid} (step-s preach step@(step-peer{pid'} sp@(step-cheat  cmc))) hpk sig ¬gen mws∈pool pcsfpk epoch≡
  -- `pid`'s state is untouched by this step
  rewrite cheatStepDNMPeerStates₁{pid = pid'}{pid' = pid} sp unit
  = oldVoteRound≤lvr preach hpk sig ¬gen mws∈prePool pcsfpkPre epoch≡
  where
  -- The cheat step could not have been where the signed message was introduced,
  -- so there must be a signed message in the pool prior to this
  mws∈prePool = ¬cheatForgeNew sp refl unit hpk mws∈pool (¬subst ¬gen (msgSameSig mws∈pool))
  -- `pid` can sign for the message in the previous system state
  pcsfpkPre   = peerCanSign-Msb4 preach step pcsfpk hpk sig mws∈prePool
oldVoteRound≤lvr{pid}{v = v} step*@(step-s{pre = pre}{post = post@._} preach step@(step-peer{pid'} sp@(step-honest{st = ppost} sps))) hpk sig ¬gen mws∈pool pcsfpk epoch≡
   with msgSameSig mws∈pool
...| refl
   with newMsg⊎msgSentB4 preach sps hpk (msgSigned mws∈pool) ¬gen (msg⊆ mws∈pool) (msg∈pool mws∈pool)
...| inj₂ msb4 = helpSentB4
   where
   pcsfpkPre : PeerCanSignForPK pre v pid _
   pcsfpkPre = peerCanSign-Msb4 preach step pcsfpk hpk sig msb4

   ovrIH : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch → v ^∙ vRound ≤ Meta.getLastVoteRound (peerStates pre pid)
   ovrIH ep≡ = oldVoteRound≤lvr{pre = pre} preach hpk sig ¬gen msb4 pcsfpkPre ep≡

   helpSentB4 : v ^∙ vRound ≤ Meta.getLastVoteRound (peerStates post pid)
   helpSentB4
      with pid ≟ pid'
   -- A step by `pid'` step cannot affect `pid`'s state
   ...| no  pid≢
      rewrite sym (pids≢StepDNMPeerStates{pre = pre} sps pid≢)
      = ovrIH epoch≡
   ...| yes pid≡ = ≤-trans (ovrIH epoch≡') lvr≤
     where
     -- If a vote signed by a peer exists in the past, and that vote has an
     -- epoch id associated to it that is the same as the peer's post-state
     -- epoch, then the peer has that same epoch id in its immediately preceding
     -- pre-state.
     epoch≡' : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch
     epoch≡' = mws∈pool⇒epoch≡ preach pcsfpkPre hpk sig ¬gen msb4

     ini : initialised pre pid' ≡ initd
     ini rewrite sym pid≡ = msg∈pool⇒initd preach pcsfpkPre hpk sig ¬gen msb4

     lvr≤ : Meta.getLastVoteRound (peerStates pre pid) ≤ Meta.getLastVoteRound (peerStates post pid)
     lvr≤
       rewrite pid≡
       |       sym (StepPeer-post-lemma{pre = pre} sp)
       = lastVotedRound-mono pid' pre preach ini sps
           (trans (subst (λ x → peerStates pre x ^∙ rmEpoch ≡ v ^∙ vEpoch) pid≡ epoch≡') (sym epoch≡))
-- The vote was newly sent this round
...| inj₁ (m∈outs , pcsfpkPost , ¬msb4)
-- ... and it really is the same vote, because there has not been a hash collision
   with sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool)
... | inj₁ nonInjSHA256 = ⊥-elim (PerReachableState.meta-sha256-cr step* nonInjSHA256)
... | inj₂ refl
   with peerCanSignPK-Inj pcsfpk pcsfpkPost refl
...| refl = ≡⇒≤ vr≡lvrPost
  where
    vr≡lvrPost : v ^∙ vRound ≡ Meta.getLastVoteRound (peerStates (StepPeer-post sp) pid)
    vr≡lvrPost
      rewrite sym (StepPeer-post-lemma sp)
      -- TODO-2: Once `newVote⇒lvr≡` is strengthened, do we have enough
      -- information to prove `VoteForRound∈`?
      = newVote⇒lvr≡{pre = pre}{pid = pid} preach sps (msg⊆ mws∈pool) m∈outs (msgSigned mws∈pool) hpk ¬gen ¬msb4

sameERasLV⇒sameId
  : ∀ {pid pid' pk}{pre : SystemState}
    → ReachableSystemState pre
    → ∀{v v' m'} → Meta-Honest-PK pk
    → just v ≡ peerStates pre pid ^∙ lSafetyData ∙ sdLastVote
    → (sig : WithVerSig pk v) -- TODO-1: Remove this parameter (not needed)
    → PeerCanSignForPK pre v pid pk
    → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre)
    → (sig' : WithVerSig pk v') → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig'))
    → v ≡L v' at vEpoch → v ≡L v' at vRound
    → v ≡L v' at vProposedId
-- Cheat steps cannot be where an honestly signed message originated.
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer sp@(step-cheat  cmc))){v}{v'}{m'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round =
  trans ih (cong (_^∙ (vdProposed ∙ biId)) ≡voteData)
  where
  -- The state of `pid` is unchanged
  ≡pidLVPre : just v ≡ peerStates pre pid ^∙ lSafetyData ∙ sdLastVote
  ≡pidLVPre = trans ≡pidLV (cong (_^∙ lSafetyData ∙ sdLastVote) (cheatStepDNMPeerStates₁ sp unit))

  -- Track down the honestly signed message which existed before.
  mws'∈pool : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
  mws'∈pool =
    ¬cheatForgeNew sp refl unit hpk
      (mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl)
      ¬gen

  -- That message has the same signature as `v'`, so it has the same vote data
  -- (unless there was a collision, which we currently assume does not occur).
  ≡voteData : msgPart mws'∈pool ≡L v' at vVoteData
  ≡voteData = ⊎-elimˡ (PerReachableState.meta-sha256-cr preach) (sameSig⇒sameVoteData sig' (msgSigned mws'∈pool) (sym ∘ msgSameSig $ mws'∈pool))

  ¬gen' : ¬ ∈GenInfo-impl genesisInfo (ver-signature ∘ msgSigned $ mws'∈pool)
  ¬gen' rewrite msgSameSig mws'∈pool = ¬gen

  -- The peer can sign for `v` now, so it can sign for `v` in the preceeding
  -- step, because there is an honestly signed for with the peer's pubkey in the
  -- current epoch already in the pool.
  pcsfpkPre : PeerCanSignForPK pre v pid pk
  pcsfpkPre = peerCanSignEp≡ (peerCanSign-Msb4 preach step (peerCanSignEp≡ pcsfpk ≡epoch) hpk sig' mws'∈pool) (sym ≡epoch)

  -- The proposal `id` for the previous existing message (and thus for v') is the same as the proposal id for `v`
  ih : v ≡L msgPart mws'∈pool at vProposedId
  ih =
    sameERasLV⇒sameId preach hpk ≡pidLVPre sig pcsfpkPre (msg⊆ mws'∈pool) (msg∈pool mws'∈pool) (msgSigned mws'∈pool) ¬gen'
      (trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData)))
      (trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData)))

sameERasLV⇒sameId{pid}{pk = pk} (step-s{pre = pre} preach step@(step-peer sp@(step-honest{pid“} sps@(step-init ini)))){v} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round
  with pid ≟ pid“
-- If this is the initialization of `pid`, then `pid` has `nothing` as its last vote
...| yes refl
  rewrite sym (StepPeer-post-lemma sp)
  = case ≡pidLV of λ ()
...| no  pid≢
-- Otherwise, no messages are generated here and the state of `pid` remains the same
  rewrite sym $ pids≢StepDNMPeerStates{pre = pre} sps pid≢
  = sameERasLV⇒sameId preach hpk ≡pidLV sig pcsfpkPre v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round
  where
  mws∈pool : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
  mws∈pool = mkMsgWithSig∈ _ _ v'⊂m' _ m'∈pool sig' refl

  pcsfpkPre : PeerCanSignForPK pre v pid pk
  pcsfpkPre = peerCanSignEp≡ (peerCanSign-Msb4 preach step (peerCanSignEp≡ pcsfpk ≡epoch) hpk sig' mws∈pool) (sym ≡epoch)
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer sp@(step-honest{pid“}{post} sps@(step-msg{_ , m} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round
   with newMsg⊎msgSentB4 preach sps hpk sig' ¬gen v'⊂m' m'∈pool
... | inj₁ (m∈outs , pcsfpk' , ¬msb4)
  with peerCanSignPK-Inj pcsfpk pcsfpk' ≡epoch
...| refl
   with v'⊂m'

... | vote∈qc vs∈qc v≈rbld qc∈m = TODO
  where
  postulate -- TODO-1: prove (waiting on: lemma to prove QC votes sent before)
    TODO : v ≡L v' at vProposedId
sameERasLV⇒sameId{pid = .pid“}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer{pid“} sp@(step-honest sps@(step-msg{_ , P pm} pm∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk ._ _ sig' ¬gen ≡epoch ≡round
  | inj₁ (m∈outs , pcsfpk' , ¬msb4) | refl | vote∈vm = ret
  where
  -- Definitions
  hpPre = peerStates pre pid“
  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPre)
  hpPos  = LBFT-post (handleProposal 0 pm) hpPre
  hpOuts = LBFT-outs (handleProposal 0 pm) hpPre

  ret : v ≡L v' at vProposedId
  ret
    with voteAttemptCorrect
  ... | Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts _)) _ =
    ⊥-elim (sendVote∉actions{outs = hpOuts}{st = hpPre} (sym noVoteMsgOuts) m∈outs)
  ... | Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect vm pid voteMsgOuts vgCorrect)) _
    with vgCorrect
  ... | Voting.mkVoteGeneratedCorrect (StateTransProps.mkVoteGenerated lv≡v _) _ = cong (_^∙ vProposedId) v≡v'
    where
    open ≡-Reasoning

    v≡v' : v ≡ v'
    v≡v' = just-injective $ begin
      just v                                                                      ≡⟨ ≡pidLV ⟩
      (peerStates (StepPeer-post{pre = pre} sp) pid“ ^∙ lSafetyData ∙ sdLastVote) ≡⟨ cong (_^∙ lSafetyData ∙ sdLastVote) (sym $ StepPeer-post-lemma{pre = pre} sp) ⟩
      (hpPos ^∙ lSafetyData ∙ sdLastVote)                                         ≡⟨ sym lv≡v ⟩
      just (vm ^∙ vmVote)                                                         ≡⟨ cong (just ∘ _^∙ vmVote) (sym $ sendVote∈actions{outs = hpOuts}{st = hpPre} (sym voteMsgOuts) m∈outs) ⟩
      just v' ∎

sameERasLV⇒sameId{pid}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer sp@(step-honest sps@(step-msg{_ , V vm} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk ._ m'∈pool sig' ¬gen ≡epoch ≡round
  | inj₁ (m∈outs , pcsfpk' , ¬msb4) | pid≡ | vote∈vm = TODO
  where
  postulate -- TODO-2: prove (waiting on: processing a vote message does not update `sdLastVote`)
    TODO : v ≡L v' at vProposedId
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer sp@(step-honest{pid“}{post} sps@(step-msg{_ , m} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round
  | inj₂ mws∈pool
  with pid ≟ pid“
...| no  pid≢
   rewrite sym $ pids≢StepDNMPeerStates{pre = pre} sps pid≢
   = trans ih (cong (_^∙ vdProposed ∙ biId) ≡voteData)
   where
   pcsfpkPre : PeerCanSignForPK pre v pid pk
   pcsfpkPre = peerCanSignEp≡ (peerCanSign-Msb4 preach step (peerCanSignEp≡ pcsfpk ≡epoch) hpk sig' mws∈pool) (sym ≡epoch)

   ≡voteData : msgPart mws∈pool ≡L v' at vVoteData
   ≡voteData = ⊎-elimˡ (PerReachableState.meta-sha256-cr preach) (sameSig⇒sameVoteData sig' (msgSigned mws∈pool) (sym ∘ msgSameSig $ mws∈pool))

   ¬gen' : ¬ ∈GenInfo-impl genesisInfo (ver-signature ∘ msgSigned $ mws∈pool)
   ¬gen' rewrite msgSameSig mws∈pool = ¬gen

   ih : v ≡L msgPart mws∈pool at vProposedId
   ih = sameERasLV⇒sameId preach{v' = msgPart mws∈pool} hpk ≡pidLV sig pcsfpkPre (msg⊆ mws∈pool) (msg∈pool mws∈pool) (msgSigned mws∈pool) ¬gen'
          (trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData)))
          (trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData)))
...| yes refl
   with v'⊂m'
... | vote∈qc vs∈qc v≈rbld qc∈m = TODO
  where
  postulate -- TODO-2: prove (note: probably some repetition with the case below)
    TODO : v ≡L v' at vProposedId
sameERasLV⇒sameId{.pid“}{pid'}{pk} (step-s{pre = pre} preach step@(step-peer{pid“} sp@(step-honest (step-msg{_ , P pm} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round
  | inj₂ mws∈pool | yes refl | vote∈vm =
  trans ih (cong (_^∙ vdProposed ∙ biId) ≡voteData)
  where
  -- Definitions
  hpPre = peerStates pre pid“
  open StateInvariants.RoundManagerInv (invariantsCorrect pid“ pre preach)
  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPre)
  hpPos  = LBFT-post (handleProposal 0 pm) hpPre
  hpOuts = LBFT-outs (handleProposal 0 pm) hpPre

  -- Lemmas
  pcsfpkPre : PeerCanSignForPK pre v pid“ pk
  pcsfpkPre = peerCanSignEp≡ (peerCanSign-Msb4 preach step (peerCanSignEp≡ pcsfpk ≡epoch) hpk sig' mws∈pool) (sym ≡epoch)

  ≡voteData : msgPart mws∈pool ≡L v' at vVoteData
  ≡voteData = ⊎-elimˡ (PerReachableState.meta-sha256-cr preach) (sameSig⇒sameVoteData sig' (msgSigned mws∈pool) (sym ∘ msgSameSig $ mws∈pool))

  ¬gen' : ¬ ∈GenInfo-impl genesisInfo (ver-signature ∘ msgSigned $ mws∈pool)
  ¬gen' rewrite msgSameSig mws∈pool = ¬gen

  -- when the last vote is the same in pre and post states
  module _ (lv≡ : hpPre ≡L hpPos at lSafetyData ∙ sdLastVote) where
    open ≡-Reasoning
    ≡pidLVPre : just v ≡ hpPre ^∙ lSafetyData ∙ sdLastVote
    ≡pidLVPre = begin
      just v                                                                      ≡⟨ ≡pidLV ⟩
      (peerStates (StepPeer-post{pre = pre} sp) pid“ ^∙ lSafetyData ∙ sdLastVote) ≡⟨ cong (_^∙ lSafetyData ∙ sdLastVote) (sym $ StepPeer-post-lemma{pre = pre} sp) ⟩
      (hpPos                                         ^∙ lSafetyData ∙ sdLastVote) ≡⟨ sym lv≡ ⟩
      (hpPre                                         ^∙ lSafetyData ∙ sdLastVote) ∎

  -- Proof
  ih : v ≡L msgPart mws∈pool at vProposedId
  ih
     with voteAttemptCorrect
  ... | Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) _
    with nvg⊎vgusc
  ... | inj₁ (StateTransProps.mkVoteNotGenerated lv≡ lvr≤) =
    sameERasLV⇒sameId preach hpk (≡pidLVPre lv≡) sig pcsfpkPre (msg⊆ mws∈pool) (msg∈pool mws∈pool) (msgSigned mws∈pool) ¬gen'
      (trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData)))
      (trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData)))
  ... | inj₂ (Voting.mkVoteGeneratedUnsavedCorrect vote (Voting.mkVoteGeneratedCorrect (StateTransProps.mkVoteGenerated lv≡v voteSrc) blockTriggered))
    with voteSrc
  ... | inj₁ (StateTransProps.mkVoteOldGenerated lvr≡ lv≡) =
    sameERasLV⇒sameId preach hpk (≡pidLVPre lv≡) sig pcsfpkPre (msg⊆ mws∈pool) (msg∈pool mws∈pool) (msgSigned mws∈pool) ¬gen'
      (trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData)))
      (trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData)))
  ... | inj₂ (StateTransProps.mkVoteNewGenerated lvr< lvr≡) =
    -- TODO-1: Use ≤-Reasoning
    ⊥-elim (<⇒≢ (≤-trans (s≤s rv'≤lvrPre) (≤-trans (≤-trans (≤-trans (s≤s (StateInvariants.SDLastVote.round≤ (StateInvariants.SafetyDataInv.lastVote sdCorrect))) lvr<) (≡⇒≤ (sym lvr≡))) (≡⇒≤ (sym (cong (_^∙ vRound) v≡vote))))) (sym ≡round))
    where
    open ≡-Reasoning
    rv'≤lvrPre : v' ^∙ vRound ≤ Meta.getLastVoteRound hpPre
    rv'≤lvrPre = oldVoteRound≤lvr preach hpk sig' ¬gen mws∈pool (peerCanSignEp≡ pcsfpkPre ≡epoch)
                   (mws∈pool⇒epoch≡ preach (peerCanSignEp≡ pcsfpkPre ≡epoch) hpk sig' ¬gen mws∈pool)

    v≡vote : v ≡ vote
    v≡vote = just-injective $ begin
      just v                                                                      ≡⟨ ≡pidLV ⟩
      (peerStates (StepPeer-post{pre = pre} sp) pid“ ^∙ lSafetyData ∙ sdLastVote) ≡⟨ cong (_^∙ lSafetyData ∙ sdLastVote) (sym $ StepPeer-post-lemma{pre = pre} sp) ⟩
      (hpPos                                         ^∙ lSafetyData ∙ sdLastVote) ≡⟨ sym lv≡v ⟩
      just vote                                                                   ∎

  ih | Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect vm pid voteMsgOuts (Voting.mkVoteGeneratedCorrect (StateTransProps.mkVoteGenerated lv≡v voteSrc) blockTriggered))) _
    with voteSrc
  ... | inj₁ (StateTransProps.mkVoteOldGenerated lvr≡ lv≡) =
    sameERasLV⇒sameId preach hpk (≡pidLVPre lv≡) sig pcsfpkPre (msg⊆ mws∈pool) (msg∈pool mws∈pool) (msgSigned mws∈pool) ¬gen'
      (trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData)))
      (trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData)))
  ... | inj₂ (StateTransProps.mkVoteNewGenerated lvr< lvr≡) =
    ⊥-elim (<⇒≢ (≤-trans (s≤s rv'≤lvrPre) (≤-trans (≤-trans (≤-trans (s≤s (StateInvariants.SDLastVote.round≤ (StateInvariants.SafetyDataInv.lastVote sdCorrect))) lvr<) (≡⇒≤ (sym lvr≡))) (≡⇒≤ (sym (cong (_^∙ vRound) v≡vote))))) (sym ≡round))
    where
    vote = vm ^∙ vmVote

    open ≡-Reasoning
    rv'≤lvrPre : v' ^∙ vRound ≤ Meta.getLastVoteRound hpPre
    rv'≤lvrPre = oldVoteRound≤lvr preach hpk sig' ¬gen mws∈pool (peerCanSignEp≡ pcsfpkPre ≡epoch)
                   (mws∈pool⇒epoch≡ preach (peerCanSignEp≡ pcsfpkPre ≡epoch) hpk sig' ¬gen mws∈pool)

    v≡vote : v ≡ vote
    v≡vote = just-injective $ begin
      just v                                                                      ≡⟨ ≡pidLV ⟩
      (peerStates (StepPeer-post{pre = pre} sp) pid“ ^∙ lSafetyData ∙ sdLastVote) ≡⟨ cong (_^∙ lSafetyData ∙ sdLastVote) (sym $ StepPeer-post-lemma{pre = pre} sp) ⟩
      (hpPos                                         ^∙ lSafetyData ∙ sdLastVote) ≡⟨ sym lv≡v ⟩
      just vote                                                                   ∎
sameERasLV⇒sameId{.pid“}{pid'}{pk} (step-s{pre = pre} preach (step-peer{pid“} (step-honest (step-msg{_ , V vm} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round | inj₂ mws∈pool | yes refl | vote∈vm = TODO
  where
  postulate -- TODO-2: prove (waiting on: vote messages do not trigger a vote message in response)
    TODO : v ≡L v' at vProposedId
sameERasLV⇒sameId{.pid“}{pid'}{pk} (step-s{pre = pre} preach (step-peer{pid“} (step-honest (step-msg{_ , C cm} m∈pool ini)))){v}{v'} hpk ≡pidLV sig pcsfpk v'⊂m' m'∈pool sig' ¬gen ≡epoch ≡round | inj₂ mws∈pool | yes refl | vote∈vm = TODO
  where
  postulate -- TODO-2: prove (waiting on: commit messages do not trigger a vote message in response)
    TODO : v ≡L v' at vProposedId

  {-
  -- NOTE: A vote being stored in `sdLastVote` does /not/ mean the vote has been
  -- sent, since the peer could have failed to save that vote in its persistent
  -- storage, leading it to drop the vote. We must additionally require that a
  -- vote for the same round as the `sdLastVote`, sent by the same peer, already
  -- exists in the pool.
  peerLastVoteSentB4
    : ∀ {pre pid v m' v' pk}
      → ReachableSystemState pre
      → just v ≡ (peerStates pre pid ^∙ (lSafetyData ∙ sdLastVote))
      → Meta-Honest-PK pk
      → (sig : WithVerSig pk v) 
      → v' ⊂Msg m' → (pid , m') ∈ msgPool pre
      → v ≡L v' at vEpoch v ≡L v' at vRound
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
  -}

votesOnce₁ : Common.IncreasingRoundObligation InitAndHandlers 𝓔
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {m} {v'} {m'} hpk (vote∈qc x x₁ x₂) m∈outs sig ¬gen ¬msb pcspkv v'⊂m' m'∈pool sig' ¬gen' eid≡ = TODO
  where
  postulate -- TODO-2: prove (waiting on: lemma that QC votes have been sent before)
    TODO : v' [ _<_ ]L v at vRound ⊎ Common.VoteForRound∈ InitAndHandlers 𝓔 pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {.(V (VoteMsg∙new v _))} {v'} {m'} hpk vote∈vm m∈outs sig ¬gen ¬msb pcspkv v'⊂m' m'∈pool sig' ¬gen' eid≡
  with handleProposalSpec.contract! 0 pm (peerStates pre pid)
... | handleProposalSpec.mkContract _ noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?) =
  ⊥-elim (sendVote∉actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym noVoteMsgOuts) m∈outs)
... | handleProposalSpec.mkContract _ noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect vm pid₁ voteMsgOuts vgCorrect)) sdEpoch≡?)
  with sendVote∈actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym voteMsgOuts) m∈outs
... | refl = ret
  where
  -- Some definitions
  step = step-peer (step-honest sps)
  rmPre  = peerStates pre pid
  rmPost = peerStates (StepPeer-post{pre = pre} (step-honest sps)) pid

  -- State invariants
  open StateInvariants
  rmInvs      = invariantsCorrect pid pre preach
  epochsMatch = RoundManagerInv.epochsMatch rmInvs
  sdInvs      = RoundManagerInv.sdCorrect   rmInvs

  -- Properties of `handleProposal`
  postLVR≡ : just v ≡ (rmPost ^∙ lSafetyData ∙ sdLastVote)
  postLVR≡ =
    trans (StateTransProps.VoteGenerated.lv≡v ∘ Voting.VoteGeneratedCorrect.state $ vgCorrect)
      (cong (_^∙ lSafetyData ∙ sdLastVote) (StepPeer-post-lemma (step-honest sps)))

  -- The proof
  m'mwsb : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
  m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl

  pcspkv'-pre : PeerCanSignForPK pre v' pid pk
  pcspkv'-pre = peerCanSign-Msb4 preach step (peerCanSignEp≡{v' = v'} pcspkv eid≡) hpk sig' m'mwsb

  rv'≤rv : v' ^∙ vRound ≤ v ^∙ vRound
  rv'≤rv =
    ≤-trans
      (oldVoteRound≤lvr preach hpk sig' ¬gen' m'mwsb pcspkv'-pre (trans rmPreEsEpoch≡ eid≡))
      realLVR≤rv
    where
    open ≡-Reasoning
    -- TODO-1 : `rmPreSdEpoch≡` can be factored out into a lemma.
    -- Something like: for any reachable state where a peer sends a vote, the
    -- epoch for that vote is the peer's sdEpoch / esEpoch.
    rmPreSdEpoch≡ : rmPre ^∙ lSafetyData ∙ sdEpoch ≡ v ^∙ vEpoch
    rmPreSdEpoch≡
       with Voting.VoteGeneratedCorrect.state vgCorrect
       |    Voting.VoteGeneratedCorrect.blockTriggered vgCorrect
    ...| StateTransProps.mkVoteGenerated lv≡v (inj₁ (StateTransProps.mkVoteOldGenerated lvr≡ lv≡)) | _
       with SDLastVote.epoch≡ ∘ SafetyDataInv.lastVote $ sdInvs
    ...| sdEpochInv rewrite trans lv≡ (sym lv≡v) = sym sdEpochInv
    rmPreSdEpoch≡
       | StateTransProps.mkVoteGenerated lv≡v (inj₂ (StateTransProps.mkVoteNewGenerated lvr< lvr≡)) | bt =
      trans sdEpoch≡? (sym ∘ proj₁ ∘ Voting.VoteMadeFromBlock⇒VoteEpochRoundIs $ bt)

    rmPreEsEpoch≡ : rmPre ^∙ rmEpochState ∙ esEpoch ≡ v ^∙ vEpoch
    rmPreEsEpoch≡ =
      begin rmPre ^∙ rmEpochState ∙ esEpoch ≡⟨ epochsMatch   ⟩
            rmPre ^∙ lSafetyData  ∙ sdEpoch ≡⟨ rmPreSdEpoch≡ ⟩
            v     ^∙ vEpoch                 ∎

    realLVR≤rv : Meta.getLastVoteRound rmPre ≤ v ^∙ vRound
    realLVR≤rv
      with Voting.VoteGeneratedCorrect.state vgCorrect
    ...| StateTransProps.mkVoteGenerated lv≡v (inj₁ (StateTransProps.mkVoteOldGenerated lvr≡ lv≡))
      rewrite trans lv≡ (sym lv≡v)
        = ≤-refl
    ...| StateTransProps.mkVoteGenerated lv≡v (inj₂ (StateTransProps.mkVoteNewGenerated lvr< lvr≡))
      with rmPre ^∙ lSafetyData ∙ sdLastVote
        |    SDLastVote.round≤ ∘ SafetyDataInv.lastVote $ sdInvs
    ...| nothing | _ = z≤n
    ...| just lv | round≤ = ≤-trans (≤-trans round≤ (<⇒≤ lvr<)) (≡⇒≤ (sym lvr≡))

  ret : v' [ _<_ ]L v at vRound ⊎ Common.VoteForRound∈ InitAndHandlers 𝓔 pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
  ret
    with <-cmp (v' ^∙ vRound) (v ^∙ vRound)
  ... | tri< rv'<rv _ _ = inj₁ rv'<rv
  ... | tri≈ _ rv'≡rv _
    = inj₂ (Common.mkVoteForRound∈ _ v' v'⊂m' pid' m'∈pool sig' (sym eid≡) rv'≡rv
        (sym (sameERasLV⇒sameId (step-s preach step) hpk postLVR≡ sig pcspkv v'⊂m' (Any-++ʳ _ m'∈pool) sig' ¬gen' eid≡ (sym rv'≡rv) )))
  ... | tri> _ _ rv'>rv = ⊥-elim (≤⇒≯ rv'≤rv rv'>rv)
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , V x} m∈pool ini) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡ = TODO
  where
  postulate -- TODO-2: prove (waiting on: vote messages do not trigger a vote message response)
    TODO : v' [ _<_ ]L v at vRound ⊎ Common.VoteForRound∈ InitAndHandlers 𝓔 pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
