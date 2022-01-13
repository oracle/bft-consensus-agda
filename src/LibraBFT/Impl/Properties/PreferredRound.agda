{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.Obligations.PreferredRound
import      LibraBFT.Concrete.Properties.Common          as Common
import      LibraBFT.Concrete.Properties.PreferredRound  as PR
open import LibraBFT.Impl.Consensus.Network              as Network
open import LibraBFT.Impl.Consensus.Network.Properties   as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
import      LibraBFT.Impl.Handle                         as Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.Handle.InitProperties
open        initHandlerSpec
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Common
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Dijkstra.All
open        ReachableSystemStateProps
open import LibraBFT.Impl.Properties.Util
open import Optics.All
open import Util.Lemmas
open import Util.PKCS
open import Util.Prelude

open Invariants
open RoundManagerTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers Handle.InitHandler.initAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions Handle.InitHandler.initAndHandlers

open import Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms
                      Handle.InitHandler.initAndHandlers
                      PeerCanSignForPK PeerCanSignForPK-stable
open        Structural impl-sps-avp


-- This module proves the two "PreferredRound" proof obligations for our handler.

module LibraBFT.Impl.Properties.PreferredRound (𝓔 : EpochConfig) where

------------------------------------------------------------------------------

preferredRound₁ : PR.ImplObligation₁ Handle.InitHandler.initAndHandlers 𝓔
preferredRound₁ {pid} {pid'} {pk = pk} {pre} preach sps@(step-init rm×acts uni) {v = v} {m = m} {v' = v'} {m' = m'}
                hpk v'⊂m' m'∈acts sig' ¬bootstrap' pcs4' v⊂m m∈pool sig ¬bootstrap eid≡ rnd< v≈vabs v'≈vabs'
                c3
  with initHandlerSpec.contract pid fakeBootstrapInfo rm×acts
...| init-contract
  with initHandlerSpec.ContractOk.isInitPM init-contract m'∈acts
...| (_ , refl , noSigs)
  with v'⊂m'
...| vote∈qc vs∈qc _ qc∈pm = ⊥-elim (noSigs vs∈qc qc∈pm)

preferredRound₁ {pid} {pid'} {pk = pk} {pre} preach sps@(step-msg {sndr , P vm} vm'∈pool ini) {v = v} {m = m} {v' = v'} {m' = m'}
                hpk v'⊂m' m'∈acts sig' ¬bootstrap' pcs4' v⊂m m∈pool sig ¬bootstrap eid≡ rnd< v≈vabs v'≈vabs'
                c3 = obm-dangerous-magic' "Extend and use handleProposalSpec.contract"

preferredRound₁ {pid} {pre = pre} preach sps@(step-msg {_ , V vm} _ _)
                _ v'⊂m' m'∈acts sig' ¬bootstrap' ¬msb _ _ _ _ _ _ _ _ _
   with v'⊂m'
...| vote∈qc vs∈qc v≈rbld qc∈m' rewrite cong _vSignature v≈rbld =
       ⊥-elim ∘′ ¬msb $ qcVoteSigsSentB4-handle pid preach sps m'∈acts qc∈m' sig' vs∈qc v≈rbld ¬bootstrap'
...| vote∈vm = ⊥-elim (sendVote∉actions{outs = hvOut}{st = hvPre} (sym noVotes) m'∈acts)
  where
  hvPre = peerStates pre pid
  hvOut = LBFT-outs (handleVote 0 vm) hvPre
  open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)

------------------------------------------------------------------------------

-- This proof is essentially the same as the votesOnce₂: no handler sends two different Votes
-- TODO-2: refactor for DRY?
preferredRound₂ : PR.ImplObligation₂ Handle.InitHandler.initAndHandlers 𝓔

preferredRound₂ {pid} _ (step-init rm×acts uni) _ v⊂m m∈acts _ _ _ _ _ _ _ _ _ _ _ _
  with initHandlerSpec.contract pid fakeBootstrapInfo rm×acts
...| init-contract
  with initHandlerSpec.ContractOk.isInitPM init-contract m∈acts
...| (_ , refl , noSigs)
  with v⊂m
...| vote∈qc vs∈qc _ qc∈pm = ⊥-elim (noSigs vs∈qc qc∈pm)

preferredRound₂ {pid}{pk = pk}{pre} rss (step-msg{sndr , m“} m“∈pool ini) {v = v}{v' = v'} hpk v⊂m m∈acts sig ¬bootstrap ¬msb4 pcsfpk v'⊂m' m'∈acts sig' ¬bootstrap' ¬msb4' _ _ round<
   with v⊂m
...| vote∈qc vs∈qc v≈rbld qc∈m rewrite cong _vSignature v≈rbld =
       ⊥-elim ∘′ ¬msb4 $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap
...| vote∈vm
  with v'⊂m'
...| vote∈qc vs∈qc' v≈rbld' qc∈m' rewrite cong _vSignature v≈rbld' =
       ⊥-elim ∘′ ¬msb4' $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m'∈acts qc∈m' sig' vs∈qc' v≈rbld' ¬bootstrap'
...| vote∈vm
  with m“
...| P pm = ⊥-elim (<⇒≢ round< (cong (_^∙ vRound) v≡v'))
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
