{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

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
import      LibraBFT.Impl.Handle                       as Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Common
open        ReachableSystemStateProps
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open Invariants
open RoundManagerTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers Handle.InitHandler.InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions Handle.InitHandler.InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms
                               Handle.InitHandler.InitAndHandlers
                               PeerCanSignForPK PeerCanSignForPK-stable
open        Structural impl-sps-avp

-- This module proves the two "VotesOnce" proof obligations for our handler.

module LibraBFT.Impl.Properties.VotesOnce (𝓔 : EpochConfig) where

newVote⇒lv≡
  : ∀ {pre : SystemState}{pid s' acts v m pk}
    → ReachableSystemState pre
    → StepPeerState pid (msgPool pre) (initialised pre)
        (peerStates pre pid) (s' , acts)
    → v ⊂Msg m → send m ∈ acts → (sig : WithVerSig pk v)
    → Meta-Honest-PK pk → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig))
    → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → LastVoteIs s' v
newVote⇒lv≡ _ (step-init initSucc uni) _ send∈acts = ⊥-elim (obm-dangerous-magic' "Use the Contract for the init handler.")
newVote⇒lv≡{pre}{pid}{s'}{v = v}{m}{pk} preach sps@(step-msg{sndr , nm} m∈pool ini) (vote∈qc{vs}{qc} vs∈qc v≈rbld qc∈m) m∈acts sig hpk ¬bootstrap ¬msb4
   with cong _vSignature v≈rbld
...| refl = ⊥-elim ∘′ ¬msb4 $ qcVoteSigsSentB4-handle pid preach sps m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap

newVote⇒lv≡{pre}{pid}{v = v} preach (step-msg{sndr , P pm} m∈pool ini) vote∈vm m∈acts sig hpk ¬bootstrap ¬msb4
  with handleProposalSpec.contract! 0 pm (msgPool pre) (peerStates pre pid)
...| handleProposalSpec.mkContract _ invalidProposal _ vac _ _
   -- TODO-2: DRY fail.  This pattern arises several times in this file, where we need to know that
   -- the proposal being processed is valid, and to use handleProposalSpec to derive a contradiction
   -- if is not.  Some are identical, some are not.
   with BlockId-correct? (pm ^∙ pmProposal)
...| no  ¬validProposal = ⊥-elim (sendVote∉actions {outs = handleOuts} {st = handlePre}
                                    (sym (proj₂ $ invalidProposal ¬validProposal)) m∈acts)
  where
  handlePre  = peerStates pre pid
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

...| yes refl
   with vac refl (nohc preach m∈pool pid ini (invariantsCorrect pid pre ini preach) refl refl)
...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , voteUnsent)) sdEpoch≡? =
  ⊥-elim (¬voteUnsent voteUnsent)
  where
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  ¬voteUnsent : ¬ Voting.VoteUnsentCorrect (peerStates pre pid) _ _ _ _
  ¬voteUnsent (Voting.mkVoteUnsentCorrect noVoteMsgOuts _) =
    sendVote∉actions{outs = handleOuts}{st = peerStates pre pid}
      (sym noVoteMsgOuts) m∈acts
...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect (VoteMsg∙new v' _) rcvr voteMsgOuts vgCorrect)) sdEpoch≡? =
  sentVoteIsPostLV
  where
  handlePost = LBFT-post (handle pid (P pm) 0) (peerStates pre pid)
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  sentVoteIsPostLV : LastVoteIs handlePost v
  sentVoteIsPostLV
    with Voting.VoteGeneratedCorrect.state vgCorrect
  ...| RoundManagerTransProps.mkVoteGenerated lv≡v _
    rewrite sym lv≡v
    = cong (just ∘ _^∙ vmVote) (sendVote∈actions{outs = handleOuts}{st = peerStates pre pid} (sym voteMsgOuts) m∈acts)

newVote⇒lv≡{pre}{pid}{s' = s'}{v = v} preach (step-msg{sndr , V vm} m∈pool ini) vote∈vm m∈outs sig hpk ¬bootstrap ¬msb4 =
  ⊥-elim (sendVote∉actions{outs = hvOut}{st = hvPre} (sym noVotes) m∈outs)
  where
  hvPre = peerStates pre pid
  hvOut = LBFT-outs (handleVote 0 vm) hvPre
  open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

oldVoteRound≤lvr
  : ∀ {pid pk v}{pre : SystemState}
    → (r : ReachableSystemState pre)
    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
    → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig))
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → PeerCanSignForPK pre v pid pk
    → (peerStates pre pid) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
    → v ^∙ vRound ≤ Meta.getLastVoteRound ((peerStates pre pid) ^∙ pssSafetyData-rm)
oldVoteRound≤lvr{pid} (step-s preach step@(step-peer{pid'} sp@(step-cheat  cmc))) hpk sig ¬bootstrap mws∈pool pcsfpk epoch≡
  -- `pid`'s state is untouched by this step
  rewrite cheatStepDNMPeerStates₁{pid = pid'}{pid' = pid} sp unit
  = oldVoteRound≤lvr preach hpk sig ¬bootstrap mws∈prePool pcsfpkPre epoch≡
  where
  -- The cheat step could not have been where the signed message was introduced,
  -- so there must be a signed message in the pool prior to this
  mws∈prePool = ¬cheatForgeNew sp refl unit hpk mws∈pool (¬subst ¬bootstrap (msgSameSig mws∈pool))
  -- `pid` can sign for the message in the previous system state
  pcsfpkPre   = PeerCanSignForPKProps.msb4 preach step pcsfpk hpk sig mws∈prePool
oldVoteRound≤lvr{pid}{v = v} step*@(step-s{pre = pre}{post = post@._} preach step@(step-peer{pid'} sp@(step-honest{st = ppost}{outs} sps))) hpk sig ¬bootstrap mws∈pool pcsfpk epoch≡
   with msgSameSig mws∈pool
...| refl
   with newMsg⊎msgSentB4 preach sps hpk (msgSigned mws∈pool) ¬bootstrap (msg⊆ mws∈pool) (msg∈pool mws∈pool)
...| Right msb4 = helpSentB4
   where
   pcsfpkPre : PeerCanSignForPK pre v pid _
   pcsfpkPre = PeerCanSignForPKProps.msb4 preach step pcsfpk hpk sig msb4

   ovrHyp : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch → v ^∙ vRound ≤ Meta.getLastVoteRound ((peerStates pre pid) ^∙ pssSafetyData-rm)
   ovrHyp ep≡ = oldVoteRound≤lvr{pre = pre} preach hpk sig ¬bootstrap msb4 pcsfpkPre ep≡

   helpSentB4 : v ^∙ vRound ≤ Meta.getLastVoteRound ((peerStates post pid) ^∙ pssSafetyData-rm)
   helpSentB4
      with pid ≟ pid'
   -- A step by `pid'` step cannot affect `pid`'s state
   ...| no  pid≢
      rewrite sym (pids≢StepDNMPeerStates{pre = pre} sps pid≢)
      = ovrHyp epoch≡
   ...| yes refl = ≤-trans (ovrHyp epochPre≡) lvr≤
     where
     -- If a vote signed by a peer exists in the past, and that vote has an
     -- epoch id associated to it that is the same as the peer's post-state
     -- epoch, then the peer has that same epoch id in its immediately preceding
     -- pre-state.
     epochPre≡ : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch
     epochPre≡ =
       ReachableSystemStateProps.mws∈pool⇒epoch≡{v = v}{ppost}{outs} preach sps
         pcsfpkPre hpk sig ¬bootstrap msb4 epoch≡'
       where
       open ≡-Reasoning
       epoch≡' : ppost ^∙ rmEpoch ≡ v ^∙ vEpoch
       epoch≡' = begin
         ppost                                         ^∙ rmEpoch ≡⟨ cong (_^∙ rmEpoch) (StepPeer-post-lemma sp) ⟩
         peerStates (StepPeer-post{pre = pre} sp) pid' ^∙ rmEpoch ≡⟨ epoch≡ ⟩
         v ^∙ vEpoch                                              ∎

     ini : initialised pre pid' ≡ initd
     ini = ReachableSystemStateProps.mws∈pool⇒initd preach pcsfpkPre hpk sig ¬bootstrap msb4

     lvr≤ : Meta.getLastVoteRound ((peerStates pre pid) ^∙ pssSafetyData-rm) ≤ Meta.getLastVoteRound ((peerStates post pid) ^∙ pssSafetyData-rm)
     lvr≤
       rewrite sym (StepPeer-post-lemma{pre = pre} sp)
       = lastVotedRound-mono pid' pre preach ini sps
           (trans epochPre≡ (sym epoch≡))
-- The vote was newly sent this round
...| Left (m∈outs , pcsfpkPost , ¬msb4)
-- ... and it really is the same vote, because there has not been a hash collision
   with sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool)
...| Left nonInjSHA256 = ⊥-elim (PerReachableState.meta-no-collision step* nonInjSHA256)
...| Right refl
   with PeerCanSignForPKProps.pidInjective pcsfpk pcsfpkPost refl
...| refl = ≡⇒≤ vr≡lvrPost
  where
    vr≡lvrPost : v ^∙ vRound ≡ Meta.getLastVoteRound ((peerStates (StepPeer-post sp) pid) ^∙ pssSafetyData-rm)
    vr≡lvrPost
      rewrite sym (StepPeer-post-lemma sp)
      with newVote⇒lv≡{pre = pre}{pid = pid} preach sps (msg⊆ mws∈pool) m∈outs (msgSigned mws∈pool) hpk ¬bootstrap ¬msb4
    ...| lastVoteIsJust
       with ppost ^∙ pssSafetyData-rm ∙ sdLastVote
    ...| nothing = absurd (just _ ≡ nothing) case lastVoteIsJust of λ ()
    ...| just _ rewrite just-injective (sym lastVoteIsJust) = refl

sameERasLV⇒sameId-lem₁ :
  ∀ {pid pid' pk s acts}{pre : SystemState}
  → ReachableSystemState pre
  → (sp : StepPeer pre pid' s acts)
  → ∀ {v v'} → Meta-Honest-PK pk
  → PeerCanSignForPK (StepPeer-post sp) v pid pk
  → (sig' : WithVerSig pk v') → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig'))
  → (mws : MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
  → v ≡L v' at vEpoch → v ≡L v' at vRound
  → Σ[ mws ∈ MsgWithSig∈ pk (ver-signature sig') (msgPool pre) ]
      (¬ ∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature ∘ msgSigned $ mws)
       × PeerCanSignForPK pre v pid pk
       × v  ≡L msgPart mws at vEpoch
       × v  ≡L msgPart mws at vRound
       × msgPart mws ≡L v' at vProposedId)
sameERasLV⇒sameId-lem₁{pid}{pid'}{pk}{pre = pre} rss sp {v}{v'} hpk pcsfpk sig' ¬bootstrap mws ≡epoch ≡round =
  mws , ¬bootstrap' , pcsfpkPre
  , trans ≡epoch (cong (_^∙ vdProposed ∙ biEpoch) (sym ≡voteData))
  , trans ≡round (cong (_^∙ vdProposed ∙ biRound) (sym ≡voteData))
  ,               cong (_^∙ vdProposed ∙ biId)    (    ≡voteData)
  where
  -- That message has the same signature as `v'`, so it has the same vote data
  -- (unless there was a collision, which we currently assume does not occur).
  ≡voteData : msgPart mws ≡L v' at vVoteData
  ≡voteData = ⊎-elimˡ (PerReachableState.meta-no-collision rss) (sameSig⇒sameVoteData sig' (msgSigned mws) (sym ∘ msgSameSig $ mws))

  ¬bootstrap' : ¬ ∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature ∘ msgSigned $ mws)
  ¬bootstrap' rewrite msgSameSig mws = ¬bootstrap

  -- The peer can sign for `v` now, so it can sign for `v` in the preceeding
  -- step, because there is an honestly signed message part for the peer's pubkey in the
  -- current epoch already in the pool.
  pcsfpkPre : PeerCanSignForPK pre v pid pk
  pcsfpkPre = PeerCanSignForPKProps.msb4-eid≡ rss (step-peer sp) hpk pcsfpk ≡epoch sig' mws

sameERasLV⇒sameId
  : ∀ {pid pid' pk}{st : SystemState}
    → ReachableSystemState st
    → ∀{v v' m'} → Meta-Honest-PK pk
    → just v ≡ peerStates st pid ^∙ pssSafetyData-rm ∙ sdLastVote
    → PeerCanSignForPK st v pid pk
    → v' ⊂Msg m' → (pid' , m') ∈ (msgPool st)
    → (sig' : WithVerSig pk v') → ¬ (∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature sig'))
    → v ≡L v' at vEpoch → v ≡L v' at vRound
    → v ≡L v' at vProposedId
-- Cheat steps cannot be where an honestly signed message originated.
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s{pre = pre} rss (step-peer sp@(step-cheat cmc))) {v}{v'}{m'} hpk ≡pidLV pcsfpk v'⊂m' m'∈pool sig' ¬bootstrap ≡epoch ≡round
   with sameERasLV⇒sameId-lem₁ rss sp hpk pcsfpk sig' ¬bootstrap mws ≡epoch ≡round
   where
   -- Track down the honestly signed message which existed before.
   mws : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
   mws = ¬cheatForgeNew sp refl unit hpk (mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl) ¬bootstrap
...| mws , ¬bootstrap' , pcsfpkPre , ≡epoch' , ≡round' , v'id≡ =
   trans (sameERasLV⇒sameId rss hpk ≡pidLVPre pcsfpkPre (msg⊆ mws) (msg∈pool mws) (msgSigned mws) ¬bootstrap' ≡epoch' ≡round') v'id≡
   where
   -- The state of `pid` is unchanged
   ≡pidLVPre : just v ≡ peerStates pre pid ^∙ pssSafetyData-rm ∙ sdLastVote
   ≡pidLVPre = trans ≡pidLV (cong (_^∙ pssSafetyData-rm ∙ sdLastVote) (cheatStepDNMPeerStates₁ sp unit))

-- Initialization steps cannot be where an honestly signed message originated
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s rss step@(step-peer{pre = pre} sp@(step-honest{pid“} sps@(step-init _ uni)))) {v}{v'}{m'} hpk ≡pidLV pcsfpk v'⊂m' m'∈pool sig' ¬bootstrap ≡epoch ≡round
   with pid ≟ pid“
   -- If this isn't `pid`, the step does not affect `pid`'s state
...| no  pid≢
   rewrite sym $ pids≢StepDNMPeerStates{pre = pre} sps pid≢
   = sameERasLV⇒sameId rss hpk ≡pidLV pcsfpkPre v'⊂m' m'∈poolb4 sig' ¬bootstrap ≡epoch ≡round
   where

   m'∈poolb4 : (pid' , m') ∈ (msgPool pre)
   m'∈poolb4 = obm-dangerous-magic' "Use the Contract for initialisation, and from that we can deduce that m' was in the pool before the step (do we have a util for this?)"

   mws : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
   mws = mkMsgWithSig∈ _ _ v'⊂m' _ m'∈poolb4 sig' refl

   pcsfpkPre : PeerCanSignForPK pre v pid pk
   pcsfpkPre = PeerCanSignForPKProps.msb4-eid≡ rss step hpk pcsfpk ≡epoch sig' mws
   -- If this is `pid`, the last vote cannot be a `just`!
...| yes refl
   rewrite sym (StepPeer-post-lemma sp)
   = absurd just v ≡ nothing case trans ≡pidLV (obm-dangerous-magic' "The Contract for the init handler should say that sdLastVote is nothing, I think!  Confirm with Harold") of λ ()

sameERasLV⇒sameId{pid}{pid'}{pk} (step-s rss (step-peer{pre = pre} sp@(step-honest{pid“} sps@(step-msg{sndr , m} m∈pool ini)))) {v}{v'} hpk ≡pidLV pcsfpk v'⊂m' m'∈pool sig' ¬bootstrap ≡epoch ≡round
   with newMsg⊎msgSentB4 rss sps hpk sig' ¬bootstrap v'⊂m' m'∈pool
-- The message has been sent before
...| Right mws'
   with sameERasLV⇒sameId-lem₁ rss sp hpk pcsfpk sig' ¬bootstrap mws' ≡epoch ≡round
...| mws , ¬bootstrap' , pcsfpkPre , ≡epoch' , ≡round' , v'id≡
   with pid ≟ pid“
   -- If this isn't `pid`, the step does not affect `pid`'s state
...| no  pid≢
   rewrite sym $ pids≢StepDNMPeerStates{pre = pre} sps pid≢
   = trans (sameERasLV⇒sameId rss hpk ≡pidLV pcsfpkPre (msg⊆ mws) (msg∈pool mws) (msgSigned mws) ¬bootstrap' ≡epoch' ≡round') v'id≡
   -- This is `pid`, so we need to know what message it was processing
...| yes refl
   rewrite sym $ StepPeer-post-lemma{pre = pre} sp
   = trans (sameERasLV⇒sameId rss hpk (≡pidLVPre m m∈pool ≡pidLV) pcsfpkPre (msg⊆ mws) (msg∈pool mws) (msgSigned mws) ¬bootstrap' ≡epoch' ≡round') v'id≡
   where
   ≡pidLVPre : (m : NetworkMsg) → (sndr , m) ∈ msgPool pre  → just v ≡ LBFT-post (handle pid m 0) (peerStates pre pid) ^∙ pssSafetyData-rm ∙ sdLastVote → just v ≡ peerStates pre pid ^∙ pssSafetyData-rm ∙ sdLastVote
   -- Last vote doesn't change when processing a vote message
   ≡pidLVPre (V vm) m∈pool ≡pidLV = begin
      just v                                 ≡⟨ ≡pidLV ⟩
      hvPos ^∙ pssSafetyData-rm ∙ sdLastVote ≡⟨ cong (_^∙ sdLastVote) (sym noSDChange) ⟩
      hvPre ^∙ pssSafetyData-rm ∙ sdLastVote ∎
      where
      open ≡-Reasoning

      hvPre = peerStates pre pid
      hvPos = LBFT-post (handleVote 0 vm) hvPre
      hvOut = LBFT-outs (handleVote 0 vm) hvPre

      open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

   -- Commit messages are only for reasoning about correctness
   ≡pidLVPre (C cm) m∈pool ≡pidLV = ≡pidLV

   ≡pidLVPre (P pm) m∈pool ≡pidLV = analyzeVoteAttempt
      where
      hpPre  = peerStates pre pid“
      hpPos  = LBFT-post (handleProposal 0 pm) hpPre

      open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm (msgPool pre) hpPre)
        renaming (rmInv to rmInvP)
      open Invariants.RoundManagerInv (invariantsCorrect pid“ pre ini rss)

      -- when the last vote is the same in pre and post states
      module OldVote (lv≡ : hpPre ≡L hpPos at pssSafetyData-rm ∙ sdLastVote) where
        open ≡-Reasoning
        ≡pidLVPre₁ : just v ≡ hpPre ^∙ pssSafetyData-rm ∙ sdLastVote
        ≡pidLVPre₁ = begin
          just v                                 ≡⟨ ≡pidLV ⟩
          hpPos ^∙ pssSafetyData-rm ∙ sdLastVote ≡⟨ sym lv≡ ⟩
          hpPre ^∙ pssSafetyData-rm ∙ sdLastVote ∎

      -- When a new vote is generated, its round is strictly greater than that of the previous vote we attempted to send.
      module NewVote
        (vote : Vote) (lv≡v : just vote ≡ hpPos ^∙ pssSafetyData-rm ∙ sdLastVote)
        (lvr< : hpPre [ _<_ ]L hpPos at pssSafetyData-rm ∙ sdLastVotedRound)
        (lvr≡ : vote ^∙ vRound ≡ hpPos ^∙ pssSafetyData-rm ∙ sdLastVotedRound)
        (sdEpoch≡ : hpPre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ pm ^∙ pmProposal ∙ bEpoch)
        (blockTriggered : Voting.VoteMadeFromBlock vote (pm ^∙ pmProposal))
        where

        -- `vote` comes from the peer handler contract
        v≡vote : v ≡ vote
        v≡vote = just-injective $ begin
          just v                                 ≡⟨ ≡pidLV ⟩
          hpPos ^∙ pssSafetyData-rm ∙ sdLastVote ≡⟨ sym lv≡v ⟩
          just vote                              ∎
          where open ≡-Reasoning

        -- The round of `v'` must be less than the round of the vote stored in `sdLastVote`
        rv'≤lvrPre : v' ^∙ vRound ≤ Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm)
        rv'≤lvrPre = oldVoteRound≤lvr rss hpk sig' ¬bootstrap mws pcsfpkPre'
                       (ReachableSystemStateProps.mws∈pool⇒epoch≡ rss (step-msg m∈pool ini)
                         pcsfpkPre' hpk sig' ¬bootstrap mws ≡epoch“)
          where
          pcsfpkPre' = peerCanSignEp≡ pcsfpkPre ≡epoch

          open ≡-Reasoning
          ≡epoch“ : hpPos ^∙ rmEpoch ≡ v' ^∙ vEpoch
          ≡epoch“ = begin
            hpPos ^∙ rmEpoch                    ≡⟨ sym noEpochChange ⟩
            hpPre ^∙ rmEpoch                    ≡⟨ rmEpochsMatch ⟩
            hpPre ^∙ pssSafetyData-rm ∙ sdEpoch ≡⟨ sdEpoch≡ ⟩
            pm    ^∙ pmProposal ∙ bEpoch        ≡⟨ sym $ Voting.VoteMadeFromBlock.epoch≡ blockTriggered ⟩
            vote  ^∙ vEpoch                     ≡⟨ cong (_^∙ vEpoch) (sym v≡vote) ⟩
            v     ^∙ vEpoch                     ≡⟨ ≡epoch ⟩
            v'    ^∙ vEpoch                     ∎

        rv'<rv : v' [ _<_ ]L v at vRound
        rv'<rv = begin
          (suc $ v' ^∙ vRound)                                      ≤⟨ s≤s rv'≤lvrPre ⟩
          (suc $ Meta.getLastVoteRound (hpPre ^∙ pssSafetyData-rm)) ≤⟨ s≤s lvRound≤ ⟩
          (suc $ hpPre ^∙ pssSafetyData-rm ∙ sdLastVotedRound)      ≤⟨ lvr< ⟩
          hpPos ^∙ pssSafetyData-rm ∙ sdLastVotedRound              ≡⟨ sym lvr≡ ⟩
          vote  ^∙ vRound                                           ≡⟨ sym (cong (_^∙ vRound) v≡vote) ⟩
          v     ^∙ vRound                                           ∎
          where
          open ≤-Reasoning
          open SafetyDataInv (SafetyRulesInv.sdInv rmSafetyRulesInv)

      analyzeVoteAttempt : just v ≡ peerStates pre pid ^∙ pssSafetyData-rm ∙ sdLastVote
      analyzeVoteAttempt
         with BlockId-correct? (pm ^∙ pmProposal)
      ...| no ¬validProposal rewrite sym (proj₁ (invalidProposal ¬validProposal)) = ≡pidLV
      ...| yes refl
         with voteAttemptCorrect refl (nohc rss m∈pool pid ini (invariantsCorrect pid pre ini rss) refl refl)
      ...| Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?
         with nvg⊎vgusc
      ...| Left (mkVoteNotGenerated lv≡ lvr≤) = OldVote.≡pidLVPre₁ lv≡
      ...| Right (Voting.mkVoteGeneratedUnsavedCorrect vote (Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered))
         with voteSrc
      ...| Left (mkVoteOldGenerated lvr≡ lv≡) = OldVote.≡pidLVPre₁ lv≡
      ...| Right (mkVoteNewGenerated lvr< lvr≡) =
         ⊥-elim (<⇒≢ (NewVote.rv'<rv vote lv≡v lvr< lvr≡ sdEpoch≡? blockTriggered) (sym ≡round))
      analyzeVoteAttempt | yes refl | Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid voteMsgOuts vgCorrect)) sdEpoch≡?
         with vgCorrect
      ...| Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered
         with voteSrc
      ...| Left (mkVoteOldGenerated lvr≡ lv≡) = OldVote.≡pidLVPre₁ lv≡
      ...| Right (mkVoteNewGenerated lvr< lvr≡) =
         ⊥-elim (<⇒≢ (NewVote.rv'<rv (vm ^∙ vmVote) lv≡v lvr< lvr≡ sdEpoch≡? blockTriggered) (sym ≡round))

-- This is the origin of the message
sameERasLV⇒sameId{pid}{pid'}{pk} (step-s rss (step-peer{pre = pre} sp@(step-honest{pid“} sps@(step-msg{sndr , m} m∈pool ini)))) {v}{v'} hpk ≡pidLV pcsfpk v'⊂m' m'∈pool sig' ¬bootstrap ≡epoch ≡round
   | Left (m'∈acts , pcsfpk' , ¬msb4)
   -- So `pid“` must be `pid`
   with PeerCanSignForPKProps.pidInjective pcsfpk pcsfpk' ≡epoch
...| refl
   with v'⊂m'
   -- QC vote signatures have been sent before
...| vote∈qc{qc = qc} vs∈qc v≈ qc∈m'
   rewrite cong _vSignature v≈
   = ⊥-elim ∘′ ¬msb4 $ qcVoteSigsSentB4-handle pid rss sps m'∈acts qc∈m' sig' vs∈qc v≈ ¬bootstrap
...| vote∈vm
   rewrite sym $ StepPeer-post-lemma{pre = pre} sp
   = sameId m m∈pool m'∈acts ≡pidLV
   where

   handlePre = peerStates pre pid

   handleOuts : NetworkMsg → List Output
   handleOuts m = LBFT-outs (handle sndr m 0) handlePre

   handlePst : NetworkMsg → RoundManager
   handlePst m = LBFT-post (handle sndr m 0) handlePre

   sameId : ∀ {sndr} m → (sndr , m) ∈ msgPool pre
          → send (V (VoteMsg∙new v' _)) ∈ outputsToActions{State = handlePre} (handleOuts m)
          → just v ≡ handlePst m ^∙ pssSafetyData-rm ∙ sdLastVote → v ≡L v' at vProposedId
   sameId (P pm) m∈pool m'∈acts ≡pidLV = analyzeVoteAttempt
     where
     open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm (msgPool pre) handlePre)

     analyzeVoteAttempt : v ≡L v' at vProposedId
     analyzeVoteAttempt
        with BlockId-correct? (pm ^∙ pmProposal)
     ...| no ¬validProposal = ⊥-elim (sendVote∉actions {outs = handleOuts (P pm)} {st = handlePre}
                                      (sym (proj₂ $ invalidProposal ¬validProposal)) m'∈acts)
     ...| yes refl
        with voteAttemptCorrect refl (nohc rss m∈pool pid ini (invariantsCorrect pid pre ini rss) refl refl)
     ...| Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , vuc)) sdEpoch≡? =
        ⊥-elim (sendVote∉actions {outs = handleOuts (P pm)} {st = handlePre} (sym $ Voting.VoteUnsentCorrect.noVoteMsgOuts vuc) m'∈acts)
     ...| Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid voteMsgOuts vgCorrect)) sdEpoch≡?
        with vgCorrect
     ... | Voting.mkVoteGeneratedCorrect (mkVoteGenerated lv≡v voteSrc) blockTriggered = cong (_^∙ vProposedId) v≡v'
        where
        open ≡-Reasoning

        v≡v' : v ≡ v'
        v≡v' = just-injective $ begin
          just v
            ≡⟨ ≡pidLV ⟩
          (handlePst (P pm)                              ^∙ pssSafetyData-rm ∙ sdLastVote)
            ≡⟨ sym lv≡v ⟩
          just (vm ^∙ vmVote)
            ≡⟨ cong (just ∘ _^∙ vmVote) (sym $ sendVote∈actions{outs = handleOuts (P pm)}{st = handlePre} (sym voteMsgOuts) m'∈acts) ⟩
          just v' ∎

   sameId (V vm) _ m'∈acts ≡pidLV =
     ⊥-elim (sendVote∉actions {outs = hvOuts} {st = peerStates pre pid} (sym noVotes) m'∈acts)
     where
     hvOuts = LBFT-outs (handleVote 0 vm) (peerStates pre pid)

     open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) handlePre)
   sameId (C x) _ ()

votesOnce₁ : Common.IncreasingRoundObligation Handle.InitHandler.InitAndHandlers 𝓔
votesOnce₁ _ (step-init initSucc uni) _ _ m∈acts = ⊥-elim (obm-dangerous-magic' "Use the Contract for the init handler.")
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {m} {v'} {m'} hpk (vote∈qc {vs} {qc} vs∈qc v≈rbld qc∈m) m∈acts sig ¬bootstrap ¬msb pcspkv v'⊂m' m'∈pool sig' ¬bootstrap' eid≡
   with cong _vSignature v≈rbld
...| refl = ⊥-elim ∘′ ¬msb $ qcVoteSigsSentB4-handle pid preach sps m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap

votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {.(V (VoteMsg∙new v _))} {v'} {m'} hpk vote∈vm m∈acts sig ¬bootstrap ¬msb pcspkv v'⊂m' m'∈pool sig' ¬bootstrap' eid≡
  with handleProposalSpec.contract! 0 pm (msgPool pre) (peerStates pre pid)
...| handleProposalSpec.mkContract _ invProp noEpochChange vac _ _
   with BlockId-correct? (pm ^∙ pmProposal)
...| no ¬validProposal = ⊥-elim (sendVote∉actions {outs = hpOut} {st = hpPre} (sym (proj₂ $ invProp ¬validProposal)) m∈acts )
   where
   hpPre  = peerStates pre pid
   hpOut  = LBFT-outs (handleProposal 0 pm) hpPre
...| yes refl
   with vac refl (nohc preach m∈pool pid ini (invariantsCorrect pid pre ini preach) refl refl)
...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡? =
     ⊥-elim (sendVote∉actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)}{st = peerStates pre pid} (sym noVoteMsgOuts) m∈acts)
...| Voting.mkVoteAttemptCorrectWithEpochReq (inj₂ (Voting.mkVoteSentCorrect vm pid₁ voteMsgOuts vgCorrect)) sdEpoch≡?
  with sendVote∈actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)}{st = peerStates pre pid} (sym voteMsgOuts) m∈acts
...| refl = ret
  where
  -- Some definitions
  step = step-peer (step-honest sps)
  rmPre  = peerStates pre pid
  rmPost = peerStates (StepPeer-post{pre = pre} (step-honest sps)) pid

  -- State invariants
  rmInvs      = invariantsCorrect pid pre ini preach
  open RoundManagerInv rmInvs

  -- Properties of `handleProposal`
  postLV≡ : just v ≡ (rmPost ^∙ pssSafetyData-rm ∙ sdLastVote)
  postLV≡ =
    trans (RoundManagerTransProps.VoteGenerated.lv≡v ∘ Voting.VoteGeneratedCorrect.state $ vgCorrect)
      (cong (_^∙ pssSafetyData-rm ∙ sdLastVote) (StepPeer-post-lemma (step-honest sps)))

  -- The proof
  m'mwsb : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
  m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl

  pcspkv'-pre : PeerCanSignForPK pre v' pid pk
  pcspkv'-pre = PeerCanSignForPKProps.msb4 preach step (peerCanSignEp≡{v' = v'} pcspkv eid≡) hpk sig' m'mwsb

  rv'≤rv : v' ^∙ vRound ≤ v ^∙ vRound
  rv'≤rv =
    ≤-trans
      (oldVoteRound≤lvr preach hpk sig' ¬bootstrap' m'mwsb pcspkv'-pre (trans rmPreEsEpoch≡ eid≡))
      realLVR≤rv
    where
    open ≡-Reasoning
    -- TODO-1 : `rmPreSdEpoch≡` can be factored out into a lemma.
    -- Something like: for any reachable state where a peer sends a vote, the
    -- epoch for that vote is the peer's sdEpoch / esEpoch.
    rmPreSdEpoch≡ : rmPre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ v ^∙ vEpoch
    rmPreSdEpoch≡
       with Voting.VoteGeneratedCorrect.state vgCorrect
       |    Voting.VoteGeneratedCorrect.blockTriggered vgCorrect
    ...| RoundManagerTransProps.mkVoteGenerated lv≡v (Left (RoundManagerTransProps.mkVoteOldGenerated lvr≡ lv≡)) | _
       with SafetyDataInv.lvEpoch≡ ∘ SafetyRulesInv.sdInv $ rmSafetyRulesInv
    ...| sdEpochInv rewrite trans lv≡ (sym lv≡v) = sym sdEpochInv
    rmPreSdEpoch≡
       | RoundManagerTransProps.mkVoteGenerated lv≡v (Right (RoundManagerTransProps.mkVoteNewGenerated lvr< lvr≡)) | bt =
      trans sdEpoch≡? (sym ∘ proj₁ ∘ Voting.VoteMadeFromBlock⇒VoteEpochRoundIs $ bt)

    rmPreEsEpoch≡ : rmPre ^∙ rmEpochState ∙ esEpoch ≡ v ^∙ vEpoch
    rmPreEsEpoch≡ =
      begin rmPre ^∙ rmEpochState ∙ esEpoch ≡⟨ rmEpochsMatch   ⟩
            rmPre ^∙ pssSafetyData-rm  ∙ sdEpoch ≡⟨ rmPreSdEpoch≡ ⟩
            v     ^∙ vEpoch                 ∎

    realLVR≤rv : Meta.getLastVoteRound (rmPre ^∙ pssSafetyData-rm) ≤ v ^∙ vRound
    realLVR≤rv
      with Voting.VoteGeneratedCorrect.state vgCorrect
    ...| RoundManagerTransProps.mkVoteGenerated lv≡v (inj₁ (RoundManagerTransProps.mkVoteOldGenerated lvr≡ lv≡))
      rewrite trans lv≡ (sym lv≡v)
        = ≤-refl
    ...| RoundManagerTransProps.mkVoteGenerated lv≡v (inj₂ (RoundManagerTransProps.mkVoteNewGenerated lvr< lvr≡))
       with rmPre ^∙ pssSafetyData-rm ∙ sdLastVote
       |    SafetyDataInv.lvRound≤ ∘ SafetyRulesInv.sdInv $ rmSafetyRulesInv
    ...| nothing | _ = z≤n
    ...| just lv | round≤ = ≤-trans (≤-trans round≤ (<⇒≤ lvr<)) (≡⇒≤ (sym lvr≡))

  ret : v' [ _<_ ]L v at vRound ⊎ Common.VoteForRound∈ Handle.InitHandler.InitAndHandlers 𝓔 pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
  ret
    with <-cmp (v' ^∙ vRound) (v ^∙ vRound)
  ...| tri< rv'<rv _ _ = Left rv'<rv
  ...| tri≈ _ rv'≡rv _
    = Right (Common.mkVoteForRound∈ _ v' v'⊂m' pid' m'∈pool sig' (sym eid≡) rv'≡rv
        (sym (sameERasLV⇒sameId (step-s preach step) hpk postLV≡ pcspkv v'⊂m' (Any-++ʳ _ m'∈pool) sig' ¬bootstrap' eid≡ (sym rv'≡rv) )))
  ... | tri> _ _ rv'>rv = ⊥-elim (≤⇒≯ rv'≤rv rv'>rv)
votesOnce₁{pid = pid}{pid'}{pk = pk}{pre = pre} preach sps@(step-msg{sndr , V vm} m∈pool ini){v}{m}{v'}{m'} hpk v⊂m m∈acts sig ¬bootstrap ¬msb vspk v'⊂m' m'∈pool sig' ¬bootstrap' eid≡
  with v⊂m
...| vote∈qc vs∈qc v≈rbld qc∈m rewrite cong _vSignature v≈rbld =
       ⊥-elim ∘′ ¬msb $ qcVoteSigsSentB4-handle pid preach sps m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap
...| vote∈vm =
  ⊥-elim (sendVote∉actions{outs = hvOut}{st = hvPre} (sym noVotes) m∈acts)
  where
  hvPre = peerStates pre pid
  hvOut = LBFT-outs (handleVote 0 vm) hvPre
  open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

votesOnce₂ : VO.ImplObligation₂ Handle.InitHandler.InitAndHandlers 𝓔
votesOnce₂ _ (step-init initSucc uni) _ _ m∈acts = ⊥-elim (obm-dangerous-magic' "Use the Contract for init handler.")
votesOnce₂{pid}{pk = pk}{pre} rss (step-msg{sndr , m“} m“∈pool ini){v}{v' = v'} hpk v⊂m m∈acts sig ¬bootstrap ¬msb4 pcsfpk v'⊂m' m'∈acts sig' ¬bootstrap' ¬msb4' pcsfpk' ≡epoch ≡round
   with v⊂m
...| vote∈qc vs∈qc v≈rbld qc∈m rewrite cong _vSignature v≈rbld =
       ⊥-elim ∘′ ¬msb4 $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap
...| vote∈vm
  with v'⊂m'
...| vote∈qc vs∈qc' v≈rbld' qc∈m' rewrite cong _vSignature v≈rbld' =
       ⊥-elim ∘′ ¬msb4' $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m'∈acts qc∈m' sig' vs∈qc' v≈rbld' ¬bootstrap'
...| vote∈vm
  with m“
...| P pm = cong (_^∙ vProposedId) v≡v'
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre
  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre)

  v≡v' : v ≡ v'
  v≡v'
    with BlockId-correct? (pm ^∙ pmProposal)
  ...| no ¬validProposal = ⊥-elim (sendVote∉actions {outs = hpOut} {st = hpPre} (sym (proj₂ $ invalidProposal ¬validProposal)) m∈acts)
  ...| yes refl
    with voteAttemptCorrect refl (nohc rss m“∈pool pid ini (invariantsCorrect pid pre ini rss) refl refl   )
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts _)) _ =
    ⊥-elim (sendVote∉actions{outs = hpOut}{st = hpPre} (sym noVoteMsgOuts) m∈acts)
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid voteMsgOuts _)) _ = begin
    v            ≡⟨        cong (_^∙ vmVote) (sendVote∈actions{outs = hpOut}{st = hpPre} (sym voteMsgOuts) m∈acts) ⟩
    vm ^∙ vmVote ≡⟨ (sym $ cong (_^∙ vmVote) (sendVote∈actions{outs = hpOut}{st = hpPre} (sym voteMsgOuts) m'∈acts)) ⟩
    v'           ∎
    where
    open ≡-Reasoning
... | V vm = ⊥-elim (sendVote∉actions{outs = hvOut}{st = hvPre} (sym noVotes) m∈acts)
  where
  hvPre = peerStates pre pid
  hvOut = LBFT-outs (handle pid (V vm) 0) hvPre
  open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)
